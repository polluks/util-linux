/*
 * SPDX-License-Identifier: GPL-2.0-or-later
 *
 * fsck.affs.c - Check the consistency of an Amiga Fast File System (FFS/OFS).
 *
 * Copyright (C) 2024 Karel Zak
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * Inspired by the AmigaOS DiskValidator and the Linux AFFS kernel driver.
 *
 * Usage: fsck.affs [options] <device>
 */

#include <stdio.h>
#include <stdarg.h>
#include <errno.h>
#include <unistd.h>
#include <string.h>
#include <fcntl.h>
#include <ctype.h>
#include <stdlib.h>
#include <getopt.h>
#include <sys/stat.h>
#include <sys/types.h>

#define XALLOC_EXIT_CODE FSCK_EX_ERROR

#include "c.h"
#include "exitcodes.h"
#include "nls.h"
#include "strutils.h"
#include "closestream.h"
#include "blkdev.h"
#include "all-io.h"
#include "ismounted.h"
#include "xalloc.h"

/* AFFS constants */
#define AFFS_BLOCK_SIZE		512
#define AFFS_ROOT_BMAPS		25
#define AFFS_NAMEMAX		30
#define AFFS_NAMEMAX_LONG	107

/* Filesystem types (boot block first 4 bytes) */
#define FS_OFS		0x444F5300
#define FS_FFS		0x444F5301
#define FS_INTLOFS	0x444F5302
#define FS_INTLFFS	0x444F5303
#define FS_DCOFS	0x444F5304
#define FS_DCFFS	0x444F5305

/* Block primary types */
#define T_SHORT		2
#define T_LIST		16
#define T_DATA		8

/* Block secondary types */
#define ST_LINKFILE	-4
#define ST_FILE		-3
#define ST_ROOT		1
#define ST_USERDIR	2
#define ST_SOFTLINK	3
#define ST_LINKDIR	4

#define AFFS_EPOCH_DELTA ((8 * 365 + 2) * 86400LL)

/* On-disk structures (all big-endian) */
struct affs_date {
	uint32_t days;
	uint32_t mins;
	uint32_t ticks;
} __attribute__((packed));

struct affs_root_head {
	uint32_t ptype;
	uint32_t spare1;
	uint32_t spare2;
	uint32_t hash_size;
	uint32_t spare3;
	uint32_t checksum;
	uint32_t hashtable[];
} __attribute__((packed));

struct affs_root_tail {
	uint32_t bm_flag;
	uint32_t bm_blk[AFFS_ROOT_BMAPS];
	uint32_t bm_ext;
	struct affs_date root_change;
	uint8_t  disk_name[32];
	uint32_t spare1;
	uint32_t spare2;
	struct affs_date disk_change;
	struct affs_date disk_create;
	uint32_t spare3;
	uint32_t spare4;
	uint32_t dcache;
	uint32_t stype;
} __attribute__((packed));

struct affs_head {
	uint32_t ptype;
	uint32_t key;
	uint32_t block_count;
	uint32_t spare1;
	uint32_t first_data;
	uint32_t checksum;
	uint32_t table[];
} __attribute__((packed));

struct affs_tail {
	uint32_t spare1;
	uint16_t uid;
	uint16_t gid;
	uint32_t protect;
	uint32_t size;
	uint8_t  comment[92];
	struct affs_date change;
	uint8_t  name[32];
	uint32_t spare2;
	uint32_t original;
	uint32_t link_chain;
	uint32_t spare[5];
	uint32_t hash_chain;
	uint32_t parent;
	uint32_t extension;
	int32_t  stype;
} __attribute__((packed));

struct affs_data_head {
	uint32_t ptype;
	uint32_t key;
	uint32_t sequence;
	uint32_t size;
	uint32_t next;
	uint32_t checksum;
	uint8_t  data[];
} __attribute__((packed));

#define AFFS_HEAD_SIZE		sizeof(struct affs_head)
#define AFFS_TAIL_SIZE		sizeof(struct affs_tail)
#define AFFS_ROOT_HEAD_SIZE	sizeof(struct affs_root_head)
#define AFFS_ROOT_TAIL_SIZE	sizeof(struct affs_root_tail)
#define AFFS_TABLE_ENTRIES	((AFFS_BLOCK_SIZE - AFFS_HEAD_SIZE - AFFS_TAIL_SIZE) / 4)

/* Global state */
static char *device_name;
static int device_fd;
static int repair, automatic, verbose, force;
static int changed;
static int errors_uncorrected;
static int fs_is_ffs;
static int fs_is_intl;
static int bitmap_valid;

/* Filesystem parameters */
static uint32_t total_blocks;
static uint32_t root_block;
static uint32_t root_from_boot;
static uint32_t hash_size;
static uint8_t  volume_name[AFFS_NAMEMAX + 1];
static uint32_t fstype;

/* Bitmap tracking (in-memory) */
static unsigned char *block_used;
static uint32_t bitmap_blocks;
/* Forward declarations */


static uint32_t be32(const uint32_t *p)
{
	const unsigned char *b = (const unsigned char *)p;
	return ((uint32_t)b[0] << 24) | ((uint32_t)b[1] << 16) |
	       ((uint32_t)b[2] << 8)  | (uint32_t)b[3];
}

static int32_t be32s(const int32_t *p)
{
	return (int32_t)be32((const uint32_t *)p);
}

static int is_affs_block(int32_t stype)
{
	return stype == ST_FILE || stype == ST_USERDIR || stype == ST_SOFTLINK ||
	       stype == ST_LINKFILE || stype == ST_LINKDIR;
}

static const char *stype_name(int32_t stype)
{
	switch (stype) {
	case ST_ROOT:     return "root";
	case ST_USERDIR:  return "directory";
	case ST_FILE:     return "file";
	case ST_LINKFILE: return "linkfile";
	case ST_LINKDIR:  return "linkdir";
	case ST_SOFTLINK: return "softlink";
	default:          return "unknown";
	}
}

static const char *fstype_name(uint32_t type)
{
	switch (type) {
	case FS_OFS:      return "OFS";
	case FS_FFS:      return "FFS";
	case FS_INTLOFS:  return "OFS (intl)";
	case FS_INTLFFS:  return "FFS (intl)";
	case FS_DCOFS:    return "OFS (dircache)";
	case FS_DCFFS:    return "FFS (dircache)";
	default:          return "unknown";
	}
}

static void __attribute__((__noreturn__))
usage(void)
{
	FILE *out = stdout;
	fputs(USAGE_HEADER, out);
	fprintf(out, _(" %s [options] <device>\n"),
		program_invocation_short_name);
	fputs(USAGE_SEPARATOR, out);
	fputs(_("Check the consistency of an Amiga FFS/OFS filesystem.\n"), out);
	fputs(USAGE_OPTIONS, out);
	fputs(_(" -a, --auto       automatic repair\n"), out);
	fputs(_(" -r, --repair     interactive repair\n"), out);
	fputs(_(" -v, --verbose    be verbose\n"), out);
	fputs(_(" -f, --force      force check even if clean\n"), out);
	fputs(_(" -n, --no         no action (check only)\n"), out);
	fputs(USAGE_SEPARATOR, out);
	fprintf(out, USAGE_HELP_OPTIONS(18));
	fprintf(out, USAGE_MAN_TAIL("fsck.affs(8)"));
	exit(FSCK_EX_OK);
}

static void __attribute__((__noreturn__))
die(const char *fmt, ...)
{
	va_list ap;
	fprintf(stderr, _("error: "));
	va_start(ap, fmt);
	vfprintf(stderr, fmt, ap);
	va_end(ap);
	fputc('\n', stderr);
	exit(FSCK_EX_ERROR);
}

static void
log_error(const char *fmt, ...)
{
	va_list ap;
	fprintf(stderr, _("Error: "));
	va_start(ap, fmt);
	vfprintf(stderr, fmt, ap);
	va_end(ap);
	fputc('\n', stderr);
	errors_uncorrected = 1;
}

static void
log_verbose(const char *fmt, ...)
{
	va_list ap;
	if (!verbose)
		return;
	va_start(ap, fmt);
	vfprintf(stdout, fmt, ap);
	va_end(ap);
	fputc('\n', stdout);
}

static void
read_block(uint32_t blk, unsigned char *buf)
{
	off_t offset = (off_t)blk * AFFS_BLOCK_SIZE;
	if (lseek(device_fd, offset, SEEK_SET) != offset) {
		log_error(_("unable to seek to block %u: %s"), blk, strerror(errno));
		memset(buf, 0, AFFS_BLOCK_SIZE);
		return;
	}
	if (read_all(device_fd, (char *)buf, AFFS_BLOCK_SIZE) != AFFS_BLOCK_SIZE) {
		log_error(_("unable to read block %u: %s"), blk, strerror(errno));
		memset(buf, 0, AFFS_BLOCK_SIZE);
	}
}

/* Compute block checksum: sum of all 32-bit words must be 0 */
static uint32_t
compute_checksum(unsigned char *buf)
{
	uint32_t *words = (uint32_t *)buf;
	int nwords = AFFS_BLOCK_SIZE / 4;
	uint32_t sum = 0;
	for (int i = 0; i < nwords; i++)
		sum += be32(&words[i]);
	return sum;
}

static int
verify_checksum(unsigned char *buf, uint32_t blk)
{
	uint32_t sum = compute_checksum(buf);
	if (sum != 0) {
		log_error(_("block %u: checksum error (sum=0x%08x)"), blk, sum);
		return 0;
	}
	return 1;
}

/* Extract BCPL string (length-prefixed, max 'maxlen' chars) */
static int
get_bstr(const uint8_t *buf, int maxlen, char *out, int outsz)
{
	int len = buf[0];
	if (len > maxlen)
		len = maxlen;
	if (len > outsz - 1)
		len = outsz - 1;
	for (int i = 0; i < len; i++)
		out[i] = buf[i + 1] >= 32 ? buf[i + 1] : '.';
	out[len] = '\0';
	return buf[0];
}

static uint32_t
hash_name(const char *name, uint32_t tabsize)
{
	uint32_t hash = strlen(name);
	for (int i = 0; name[i]; i++) {
		unsigned char c = (unsigned char)name[i];
		if (fs_is_intl) {
			/* International mode: lowercase only A-Z */
			if (c >= 'A' && c <= 'Z')
				c += 'a' - 'A';
		} else {
			c = toupper(c);
		}
		hash = (hash * 13 + c) & 0x7FF;
	}
	return hash % tabsize;
}

/* Parse the boot block to determine filesystem type and root block */
static int
read_boot_block(void)
{
	unsigned char buf[AFFS_BLOCK_SIZE];

	read_block(0, buf);
	fstype = be32((uint32_t *)buf);
	root_from_boot = be32((uint32_t *)(buf + 8));

	if (fstype == FS_OFS || fstype == FS_INTLOFS || fstype == FS_DCOFS) {
		fs_is_ffs = 0;
	} else if (fstype == FS_FFS || fstype == FS_INTLFFS || fstype == FS_DCFFS) {
		fs_is_ffs = 1;
	} else {
		log_error(_("unknown filesystem type 0x%08x on %s"),
			  fstype, device_name);
		return 0;
	}

	fs_is_intl = (fstype == FS_INTLOFS || fstype == FS_INTLFFS ||
		      fstype == FS_DCOFS || fstype == FS_DCFFS);

	if (verbose) {
		printf(_("Filesystem type: %s\n"), fstype_name(fstype));
		if (root_from_boot)
			printf(_("Root block (from boot): %u\n"), root_from_boot);
	}

	return 1;
}

/* Determine total blocks from device size */
static int
get_device_size(void)
{
	struct stat st;

	if (fstat(device_fd, &st) != 0)
		die(_("can't stat %s: %s"), device_name, strerror(errno));

	if (S_ISBLK(st.st_mode)) {
		unsigned long long bytes;
		if (blkdev_get_size(device_fd, &bytes) != 0)
			die(_("can't get size of %s: %s"), device_name,
			    strerror(errno));
		total_blocks = bytes / AFFS_BLOCK_SIZE;
	} else if (S_ISREG(st.st_mode)) {
		total_blocks = st.st_size / AFFS_BLOCK_SIZE;
	} else {
		die(_("%s is not a block device or regular file"), device_name);
	}

	if (total_blocks < 4) {
		log_error(_("%s: too small (%u blocks)"), device_name, total_blocks);
		return 0;
	}

	if (verbose)
		printf(_("Total blocks: %u\n"), total_blocks);

	return 1;
}

/* Read and validate the root block */
static int
read_root_block(void)
{
	unsigned char buf[AFFS_BLOCK_SIZE];
	struct affs_root_head *rh;
	struct affs_root_tail *rt;
	uint32_t bm_flag_val, stype_val;
	char vname[256];

	uint32_t root_candidates[2];
	int n_candidates = 0;

	root_candidates[n_candidates++] = total_blocks / 2;
	if (root_from_boot > 0 && root_from_boot < total_blocks &&
	    root_from_boot != total_blocks / 2)
		root_candidates[n_candidates++] = root_from_boot;

	for (int attempt = 0; attempt < n_candidates; attempt++) {
		root_block = root_candidates[attempt];
		read_block(root_block, buf);

		rh = (struct affs_root_head *)buf;
		if (be32(&rh->ptype) != T_SHORT)
			continue;

		hash_size = be32(&rh->hash_size);
		if (hash_size < 4 || hash_size > AFFS_TABLE_ENTRIES)
			continue;

		if (compute_checksum(buf) != 0)
			continue;

		/* Root tail is at end of block */
		rt = (struct affs_root_tail *)(buf + AFFS_BLOCK_SIZE - AFFS_ROOT_TAIL_SIZE);
		stype_val = be32(&rt->stype);
		if (stype_val != ST_ROOT)
			continue;

		goto found_root;
	}

	log_error(_("no valid root block found (tried block %u"),
		  root_candidates[0]);
	if (n_candidates > 1)
		log_error(_(" and block %u"), root_candidates[1]);
	log_error(_(")"));
	return 0;

found_root:

	bm_flag_val = be32(&rt->bm_flag);
	bitmap_valid = (bm_flag_val == (uint32_t)-1);

	if (verbose) {
		printf(_("Root block: %u\n"), root_block);
		printf(_("Hash table size: %u\n"), hash_size);
		printf(_("Bitmap valid: %s\n"), bitmap_valid ? _("yes") : _("no"));
	}

	/* Extract volume name */
	get_bstr(rt->disk_name, AFFS_NAMEMAX, vname, sizeof(vname));
	strncpy((char *)volume_name, vname, AFFS_NAMEMAX);
	volume_name[AFFS_NAMEMAX] = '\0';

	if (verbose)
		printf(_("Volume name: %s\n"), volume_name);

	return 1;
}

/* Read and verify a bitmap block */
static int
read_bitmap_block(uint32_t blk, unsigned char *buf)
{
	read_block(blk, buf);

	/* Bitmap block checksum is at word 0 */
	uint32_t sum = 0;
	uint32_t *words = (uint32_t *)buf;
	int nwords = AFFS_BLOCK_SIZE / 4;
	for (int i = 0; i < nwords; i++)
		sum += be32(&words[i]);
	if (sum != 0) {
		log_error(_("bitmap block %u: checksum error"), blk);
		return 0;
	}
	return 1;
}

/* Build in-memory block usage map from the on-disk bitmap */
static int
build_bitmap_usage(void)
{
	unsigned char buf[AFFS_BLOCK_SIZE];
	struct affs_root_tail *rt;
	int n_bitmap_blocks = 0;
	uint32_t bm_blks[AFFS_ROOT_BMAPS];
	uint32_t bm_ext;
	int bitmap_ok = 1;

	/* Read root block tail to get bitmap pointers */
	read_block(root_block, buf);
	rt = (struct affs_root_tail *)(buf + AFFS_BLOCK_SIZE - AFFS_ROOT_TAIL_SIZE);

	for (int i = 0; i < AFFS_ROOT_BMAPS; i++)
		bm_blks[i] = be32(&rt->bm_blk[i]);
	bm_ext = be32(&rt->bm_ext);

	block_used = xcalloc(total_blocks, 1);

	/* Mark boot blocks as used (not covered by bitmap) */
	block_used[0] = 1;
	block_used[1] = 1;

	/* Count bitmap blocks */
	for (int i = 0; i < AFFS_ROOT_BMAPS; i++) {
		if (bm_blks[i] == 0 || bm_blks[i] >= total_blocks)
			break;
		n_bitmap_blocks++;
	}

	/* If bm_ext exists, follow the extension chain */
	if (bm_ext != 0 && bm_ext < total_blocks) {
		uint32_t next = bm_ext;
		while (next != 0 && next < total_blocks) {
			n_bitmap_blocks++;
			read_block(next, buf);
			/* Extended bitmap block: first word is checksum, rest are pointers */
			next = be32((uint32_t *)(buf + AFFS_BLOCK_SIZE - 4));
		}
	}

	bitmap_blocks = n_bitmap_blocks;
	log_verbose(_("Bitmap blocks: %d"), n_bitmap_blocks);

	/* Mark bitmap blocks themselves as used */
	for (int i = 0; i < AFFS_ROOT_BMAPS && bm_blks[i]; i++) {
		if (bm_blks[i] < total_blocks)
			block_used[bm_blks[i]] = 1;
	}
	if (bm_ext && bm_ext < total_blocks) {
		uint32_t next = bm_ext;
		while (next && next < total_blocks) {
			block_used[next] = 1;
			read_block(next, buf);
			next = be32((uint32_t *)(buf + AFFS_BLOCK_SIZE - 4));
		}
	}

	/* Now read the bitmap data */
	uint32_t bm_chain = bm_ext;
	for (int i = 0; i < n_bitmap_blocks; i++) {
		uint32_t bb;
		if (i < AFFS_ROOT_BMAPS)
			bb = bm_blks[i];
		else {
			bb = bm_chain;
			if (bb == 0 || bb >= total_blocks)
				break;
		}

		if (bb == 0 || bb >= total_blocks)
			continue;

		unsigned char bmbuf[AFFS_BLOCK_SIZE];
		if (!read_bitmap_block(bb, bmbuf))
			continue;

		/*
		 * Extended bitmap blocks use the last 4 bytes as a chain pointer,
		 * so they have 4032 bits of bitmap data instead of 4064.
		 */
		int bits;
		if (i < AFFS_ROOT_BMAPS)
			bits = (AFFS_BLOCK_SIZE - 4) * 8;
		else
			bits = (AFFS_BLOCK_SIZE - 8) * 8;

		/* Get next in chain (last word of extended bitmap) */
		if (i >= AFFS_ROOT_BMAPS)
			bm_chain = be32((uint32_t *)(bmbuf + AFFS_BLOCK_SIZE - 4));

		/* Bitmap data starts at word 1 (after checksum) */
		uint32_t *bm_words = (uint32_t *)bmbuf;
		uint32_t base_blk = i * ((AFFS_BLOCK_SIZE - 4) * 8) + 2;

		for (int b = 0; b < bits; b++) {
			uint32_t blk_num = base_blk + b;
			if (blk_num >= total_blocks)
				break;
			int word_idx = 1 + b / 32;
			int bit_idx = 31 - (b % 32);
			int is_free = (be32(&bm_words[word_idx]) >> bit_idx) & 1;
			if (is_free && blk_num < total_blocks)
				block_used[blk_num] = (block_used[blk_num] ? 2 : 0);
			else if (blk_num < total_blocks)
				block_used[blk_num] = (block_used[blk_num] ? 2 : 1);
		}
	}

	return bitmap_ok;
}

/* Check all blocks reachable from a header block's data pointers */
static void
check_data_blocks(unsigned char *buf, uint32_t blk, int32_t stype)
{
	struct affs_head *h = (struct affs_head *)buf;
	uint32_t block_count = be32(&h->block_count);
	uint32_t extension = be32((uint32_t *)(buf + AFFS_BLOCK_SIZE - AFFS_TAIL_SIZE
				  + offsetof(struct affs_tail, extension)));

	if (block_count > AFFS_TABLE_ENTRIES) {
		log_error(_("block %u: bad block count %u"), blk, block_count);
		return;
	}

	/* Check direct data block pointers */
	for (uint32_t i = 0; i < block_count && i < AFFS_TABLE_ENTRIES; i++) {
		/* Stored in reverse order: table[AFFS_TABLE_ENTRIES-1] = first */
		uint32_t db = be32(&h->table[AFFS_TABLE_ENTRIES - 1 - i]);
		if (db == 0)
			continue;
		if (db >= total_blocks) {
			log_error(_("block %u: data block %u out of range"), blk, db);
			continue;
		}
		if (block_used[db] == 2) {
			log_error(_("block %u: data block %u already claimed"), blk, db);
		} else if (block_used[db] == 0) {
			log_error(_("block %u: data block %u not marked in bitmap"), blk, db);
		} else {
			block_used[db] = 2;
		}

		/* For OFS, verify data block header */
		if (!fs_is_ffs && db > 0 && db < total_blocks) {
			unsigned char dbuf[AFFS_BLOCK_SIZE];
			read_block(db, dbuf);
			struct affs_data_head *dh = (struct affs_data_head *)dbuf;
			if (be32(&dh->ptype) != T_DATA)
				log_error(_("data block %u: bad type %u (expected %u)"),
					  db, be32(&dh->ptype), T_DATA);
			else if (be32(&dh->key) != blk)
				log_error(_("data block %u: header_key %u != owner %u"),
					  db, be32(&dh->key), blk);
		}
	}

	/* Check extension blocks */
	uint32_t ext = extension;
	while (ext != 0) {
		if (ext >= total_blocks) {
			log_error(_("block %u: extension block %u out of range"), blk, ext);
			break;
		}
		if (block_used[ext] == 2) {
			log_error(_("block %u: extension block %u already claimed"), blk, ext);
			break;
		}
		block_used[ext] = 2;

		unsigned char ebuf[AFFS_BLOCK_SIZE];
		read_block(ext, ebuf);

		if (be32((uint32_t *)ebuf) != T_LIST) {
			log_error(_("extension block %u: bad type %u (expected %u)"),
				  ext, be32((uint32_t *)ebuf), T_LIST);
			break;
		}
		if (!verify_checksum(ebuf, ext))
			break;

		struct affs_head *eh = (struct affs_head *)ebuf;
		uint32_t ecnt = be32(&eh->block_count);
		if (ecnt > AFFS_TABLE_ENTRIES) {
			log_error(_("extension block %u: bad block count %u"), ext, ecnt);
			break;
		}
		for (uint32_t i = 0; i < ecnt && i < AFFS_TABLE_ENTRIES; i++) {
			uint32_t db = be32(&eh->table[AFFS_TABLE_ENTRIES - 1 - i]);
			if (db == 0)
				continue;
			if (db >= total_blocks) {
				log_error(_("block %u (ext %u): data block %u out of range"),
					  blk, ext, db);
				continue;
			}
			if (block_used[db] == 2)
				log_error(_("block %u (ext %u): data block %u already claimed"),
					  blk, ext, db);
			else if (block_used[db] == 0)
				log_error(_("block %u: data block %u not marked in bitmap"),
					  blk, db);
			else
				block_used[db] = 2;

			if (!fs_is_ffs && db > 0 && db < total_blocks) {
				unsigned char dbuf[AFFS_BLOCK_SIZE];
				read_block(db, dbuf);
				if (be32((uint32_t *)dbuf) != T_DATA)
					log_error(_("data block %u: bad type"), db);
			}
		}

		/* Get next extension from tail of extension block */
		ext = be32((uint32_t *)(ebuf + AFFS_BLOCK_SIZE - AFFS_TAIL_SIZE
			   + offsetof(struct affs_tail, extension)));
	}

	/* For symlinks, the data is inline (no data blocks needed) */
	if (stype == ST_SOFTLINK && block_count == 0)
		return;
}

/* Recursively check a directory block */
static void
check_directory(uint32_t blk, int depth)
{
	unsigned char buf[AFFS_BLOCK_SIZE];
	struct affs_head *h;
	struct affs_tail *t;
	int32_t stype;
	char fname[256];
	uint32_t hash_chain;
	uint32_t parent;
	uint32_t expected_hash;

	if (depth > 256) {
		log_error(_("directory too deep at block %u (symlink loop?)"), blk);
		return;
	}

	if (blk >= total_blocks || blk == 0) {
		log_error(_("invalid directory block %u"), blk);
		return;
	}

	if (block_used[blk] == 2) {
		log_error(_("directory block %u already visited (loop?)"), blk);
		return;
	}
	block_used[blk] = 2;

	read_block(blk, buf);

	if (be32((uint32_t *)buf) != T_SHORT) {
		log_error(_("directory block %u: bad type"), blk);
		return;
	}

	if (!verify_checksum(buf, blk))
		return;

	t = (struct affs_tail *)(buf + AFFS_BLOCK_SIZE - AFFS_TAIL_SIZE);
	stype = be32s(&t->stype);

	if (stype != ST_USERDIR && stype != ST_ROOT && stype != ST_LINKDIR) {
		log_error(_("block %u: expected directory, got %s"), blk, stype_name(stype));
		return;
	}

	/* Check parent pointer (unless root) */
	if (stype != ST_ROOT) {
		parent = be32(&t->parent);
		if (parent >= total_blocks)
			log_error(_("block %u: parent pointer %u out of range"), blk, parent);
		else if (parent != root_block && parent > 0 && !block_used[parent])
			log_error(_("block %u: parent %u not visited"), blk, parent);
	}

	/* Extract name */
	if (stype != ST_ROOT) {
		get_bstr(t->name, AFFS_NAMEMAX, fname, sizeof(fname));
		if (verbose > 1)
			printf(_("  %*s%s (block %u)\n"), depth * 2, "", fname, blk);
	} else {
		strcpy(fname, "/");
		if (verbose > 1)
			printf(_("  / (root block %u)\n"), blk);
	}

	/* For a directory, the hash table is in the same location as data table */
	h = (struct affs_head *)buf;
	uint32_t hsize = (stype == ST_ROOT) ? hash_size : AFFS_TABLE_ENTRIES;

	/* Process hash chain for each slot */
	for (uint32_t i = 0; i < hsize && i < AFFS_TABLE_ENTRIES; i++) {
		uint32_t entry = be32(&h->table[i]);
		while (entry != 0) {
			if (entry >= total_blocks) {
				log_error(_("block %u: hash chain entry %u out of range"),
					  blk, entry);
				break;
			}

			unsigned char ebuf[AFFS_BLOCK_SIZE];
			read_block(entry, ebuf);
			if (be32((uint32_t *)ebuf) != T_SHORT) {
				log_error(_("hash chain block %u: bad type"), entry);
				break;
			}

			struct affs_tail *et = (struct affs_tail *)(ebuf + AFFS_BLOCK_SIZE
								   - AFFS_TAIL_SIZE);
			int32_t estype = be32s(&et->stype);

			if (!is_affs_block(estype)) {
				log_error(_("block %u: bad secondary type %d in hash chain"),
					  entry, estype);
				break;
			}

			/* Check hash consistency */
			char ename[256];
			get_bstr(et->name, AFFS_NAMEMAX, ename, sizeof(ename));
			expected_hash = hash_name(ename, hsize);
			if (expected_hash != i) {
				log_error(_("block %u (%s): bad hash (expected %u, slot %u)"),
					  entry, ename, expected_hash, i);
			}

			/* Verify parent pointer for non-root entries */
			if (estype != ST_ROOT) {
				uint32_t eparent = be32(&et->parent);
				if (eparent != blk) {
					log_error(_("block %u (%s): parent mismatch "
						    "(parent=%u, expected=%u)"),
						  entry, ename, eparent, blk);
				}
			}

			/* Recurse into subdirectories */
			if (estype == ST_USERDIR || estype == ST_LINKDIR) {
				check_directory(entry, depth + 1);
			} else if (estype == ST_FILE || estype == ST_LINKFILE) {
				block_used[entry] = 2;
				check_data_blocks(ebuf, entry, estype);
			} else if (estype == ST_SOFTLINK) {
				block_used[entry] = 2;
			}

			hash_chain = be32(&et->hash_chain);
			if (hash_chain != 0 && hash_chain < total_blocks)
				entry = hash_chain;
			else
				break;
		}
	}
}

/* Main checking routine */
static void
check_fs(void)
{
	unsigned char buf[AFFS_BLOCK_SIZE];
	struct affs_root_tail *rt;

	log_verbose(_("Checking filesystem..."));

	/* Read root block tail for initial bitmap pointers */
	read_block(root_block, buf);
	rt = (struct affs_root_tail *)(buf + AFFS_BLOCK_SIZE - AFFS_ROOT_TAIL_SIZE);

	if (!bitmap_valid || force) {
		if (!bitmap_valid && verbose)
			printf(_("Bitmap is marked invalid, rebuilding...\n"));
		if (force && verbose)
			printf(_("Force checking, rebuilding bitmap...\n"));

		/* Mark boot blocks, bitmap blocks and root block as used */
		block_used[0] = 1;
		block_used[1] = 1;
		block_used[root_block] = 1;

		for (int i = 0; i < AFFS_ROOT_BMAPS; i++) {
			uint32_t bb = be32(&rt->bm_blk[i]);
			if (bb == 0 || bb >= total_blocks)
				break;
			block_used[bb] = 1;
		}
		if (be32(&rt->bm_ext) != 0 && be32(&rt->bm_ext) < total_blocks) {
			uint32_t next = be32(&rt->bm_ext);
			while (next != 0 && next < total_blocks) {
				block_used[next] = 1;
				read_block(next, buf);
				next = be32((uint32_t *)(buf + AFFS_BLOCK_SIZE - 4));
			}
		}
	}

	/* Walk the entire filesystem tree from root */
	check_directory(root_block, 0);

	/* Now check if bitmap matches our walk */
	if (block_used) {
		uint32_t nclaimed = 0, nfree = 0;

		for (uint32_t i = 0; i < total_blocks; i++) {
			if (block_used[i] == 1) {
				/* Block marked used in bitmap but not claimed by any file */
				if (i >= 2 && i != root_block) {
					/* Skip bitmap blocks */
					int is_bm = 0;
					read_block(root_block, buf);
					rt = (struct affs_root_tail *)(buf + AFFS_BLOCK_SIZE
								      - AFFS_ROOT_TAIL_SIZE);
					for (int j = 0; j < AFFS_ROOT_BMAPS; j++) {
						if (be32(&rt->bm_blk[j]) == i)
							is_bm = 1;
					}
					if (!is_bm && be32(&rt->bm_ext) != i) {
						log_error(_("block %u: allocated in bitmap "
							    "but not referenced"), i);
						nclaimed++;
					}
				}
			} else if (block_used[i] == 0) {
				nfree++;
			}
		}
		if (nclaimed && verbose)
			printf(_("Orphaned bitmap blocks: %u\n"), nclaimed);

		if (verbose) {
			printf(_("Total blocks: %u, used: %u, free: %u\n"),
			       total_blocks,
			       total_blocks - nfree,
			       nfree);
		}
	}
}

/* Interactive yes/no prompt */
static int
ask(const char *question, int def)
{
	char input[64];
	if (!repair) {
		printf("\n");
		errors_uncorrected = 1;
		return 0;
	}
	if (automatic) {
		printf("\n");
		if (!def)
			errors_uncorrected = 1;
		return def;
	}
	printf(def ? _("%s (y/n)? ") : _("%s (n/y)? "), question);
	fflush(stdout);
	if (!fgets(input, sizeof(input), stdin))
		return def;
	if (input[0] == 'y' || input[0] == 'Y')
		return 1;
	if (input[0] == 'n' || input[0] == 'N')
		return 0;
	return def;
}

/* Check if device is moun ted */
static void
check_mount(void)
{
	int cont;

	if (!is_mounted(device_name))
		return;

	printf(_("%s is mounted.\t "), device_name);
	if (isatty(STDIN_FILENO) && isatty(STDOUT_FILENO))
		cont = ask(_("Do you really want to continue"), 0);
	else
		cont = 0;
	if (!cont) {
		printf(_("check aborted.\n"));
		exit(FSCK_EX_OK);
	}
}

int
main(int argc, char **argv)
{
	int c;
	int no_action = 0;
	static const struct option longopts[] = {
		{ "auto",      no_argument,       NULL, 'a' },
		{ "repair",    no_argument,       NULL, 'r' },
		{ "verbose",   no_argument,       NULL, 'v' },
		{ "force",     no_argument,       NULL, 'f' },
		{ "no",        no_argument,       NULL, 'n' },
		{ "version",   no_argument,       NULL, 'V' },
		{ "help",      no_argument,       NULL, 'h' },
		{ NULL, 0, NULL, 0 }
	};

	setlocale(LC_ALL, "");
	bindtextdomain(PACKAGE, LOCALEDIR);
	textdomain(PACKAGE);
	close_stdout_atexit();
	strutils_set_exitcode(FSCK_EX_USAGE);

	while ((c = getopt_long(argc, argv, "arvfVhn", longopts, NULL)) != -1) {
		switch (c) {
		case 'a':
			automatic = 1;
			repair = 1;
			break;
		case 'r':
			automatic = 0;
			repair = 1;
			break;
		case 'v':
			verbose++;
			break;
		case 'f':
			force = 1;
			break;
		case 'n':
			no_action = 1;
			repair = 0;
			break;
		case 'V':
			print_version(FSCK_EX_OK);
		case 'h':
			usage();
		default:
			errtryhelp(FSCK_EX_USAGE);
		}
	}

	argc -= optind;
	argv += optind;

	if (argc < 1) {
		warnx(_("no device specified"));
		errtryhelp(FSCK_EX_USAGE);
	}

	device_name = argv[0];
	check_mount();

	if (repair && !automatic && no_action)
		repair = 0;

	if (repair && !automatic && (!isatty(STDIN_FILENO) || !isatty(STDOUT_FILENO)))
		die(_("need terminal for interactive repairs"));

	device_fd = open(device_name, (repair && !no_action) ? O_RDWR : O_RDONLY);
	if (device_fd < 0)
		die(_("cannot open %s: %s"), device_name, strerror(errno));

	if (!get_device_size())
		exit(FSCK_EX_ERROR);

	if (!read_boot_block())
		exit(FSCK_EX_ERROR);

	if (!read_root_block())
		exit(FSCK_EX_ERROR);

	/* Build usage map from bitmap */
	build_bitmap_usage();

	/* Do the actual check */
	check_fs();

	if (changed) {
		printf(_("----------------------------\n"
			 "FILE SYSTEM HAS BEEN CHANGED\n"
			 "----------------------------\n"));
		for (c = 0; c < 3; c++)
			sync();
	}

	if (close_fd(device_fd) != 0)
		err(FSCK_EX_ERROR, _("write failed"));

	int retcode = FSCK_EX_OK;
	if (changed)
		retcode += FSCK_EX_NONDESTRUCT;
	if (errors_uncorrected)
		retcode += FSCK_EX_UNCORRECTED;

	return retcode;
}
