/*

  grepcidr 2.99 - Filter IP addresses matching IPv4 and IPv6 CIDR specification
  Parts copyright (C) 2004, 2005  Jem E. Berkes <jberkes@pc-tools.net>
  	www.sysdesign.ca
  Somewhat rewritten by John Levine <johnl@taugh.com>

  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
  $Header: /Users/johnl/grepcidr-2.991/RCS/grepcidr.c,v 1.5 2015/10/25 15:11:06 johnl Exp $
*/


#define _WITH_GETLINE /* hint for FreeBSD */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <getopt.h>
#include <ctype.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <assert.h>

#define EXIT_OK		0
#define EXIT_NOMATCH	1
#define EXIT_ERROR	2

#define TXT_VERSION	"grepcidr 2.991\nParts copyright (C) 2004, 2005  Jem E. Berkes <jberkes@pc-tools.net>\n"
#define TXT_USAGE	"Usage:\n" \
			"\tgrepcidr [-V] [-cCDvhais] PATTERN [FILE...]\n" \
			"\tgrepcidr [-V] [-cCDvhais] [-e PATTERN | -f FILE] [FILE...]\n"
#define MAXFIELD	512
#define TOKEN_SEPS	"\t,\r\n"	/* so user can specify multiple patterns on command line */
#define INIT_NETWORKS	8192

/*
	Specifies a network. Whether originally in CIDR format (IP/mask)
	or a range of IPs (IP_start-IP_end), spec is converted to a range.
	The range is min to max (32-bit or 128 bit IPs) inclusive.
*/
struct netspec
{
	unsigned int min;
	unsigned int max;
};

typedef struct v6addr { unsigned char a[16]; } v6addr;

/* redefine this if your memcmp is slow, but it probably isn't */
#define v6cmp(a1, a2) memcmp((a1).a,(a2).a,16)

struct netspec6
{
	v6addr min;
	v6addr max;
};

/* Global variables */
static unsigned int npatterns = 0;		/* total patterns in array */
static unsigned int n6patterns = 0;		/* total patterns in v6 array */
static unsigned int capacity = 0;		/* current capacity of array */
static unsigned int capacity6 = 0;		/* current capacity of v6 array */
static struct netspec* array = NULL;		/* array of patterns, network specs */
static struct netspec6* array6 = NULL;		/* array of patterns, v6 network specs */
static unsigned int counting = 0;		/* when non-zero, counts matches */
static int invert = 0;				/* flag for inverted mode */
static int anchor = 0;				/* anchor matches at beginning of line */
static int nonames = 0;				/* don't show filenames */
static int nmatch = 0;				/* count of matches for exit code */
static int igbadpat = 0;			/* ignore bad patterns */
static int sloppy = 0;				/* don't complain about sloppy CIDR */
static int cidrsearch = 0;			/* parse and match CIDR in haystack */
static int didrsearch = 0;			/* match CIDR if overlaps with haystack */
static int quick = 0;				/* quick match, ignore v4 with dots before or after */

static void scan_block(char *bp, size_t blen, const char *fn);
static void scan_read(FILE *f, const char *fn);
static int applymask6(const v6addr ahi, int size, struct netspec6 *spec);

/* for getline */
char *linep = NULL;
size_t linesize;

/*
	Insert new spec inside array of network spec
	Dynamically grow array buffer as needed
*/
void array_insert(struct netspec* newspec)
{
	/* Initial array allocation */
	if(!array) {
		capacity = INIT_NETWORKS;
		array = (struct netspec*) malloc(capacity*sizeof(struct netspec));
		if(!array) {
			perror("Out of memory");
			exit(EXIT_ERROR);
		}
	}
	if (npatterns == capacity)
	{
		capacity *= 2;
		array = (struct netspec *)realloc(array, capacity*sizeof(struct netspec));
		if(!array) {
			perror("Out of memory");
			exit(EXIT_ERROR);
		}
	}
	array[npatterns++] = *newspec;
}

void array_insert6(struct netspec6* newspec)
{
	/* Initial array allocation */
	if(!array6) {
		capacity6 = INIT_NETWORKS;
		array6 = (struct netspec6*) malloc(capacity6*sizeof(struct netspec6));
		if(!array6) {
			perror("Out of memory");
			exit(EXIT_ERROR);
		}
	}
	if (n6patterns == capacity6)
	{
		capacity6 *= 2;
		array6 = (struct netspec6 *)realloc(array6, capacity6*sizeof(struct netspec6));
		if(!array6) {
			perror("Out of memory");
			exit(EXIT_ERROR);
		}
	}
	array6[n6patterns++] = *newspec;
}

/*
	Given string, fills in the struct netspec (must be allocated)
	Accept CIDR IP/mask format or IP_start-IP_end range.
	Returns true (nonzero) on success, false (zero) on failure.
*/
int net_parse(const char* line, struct netspec* spec)
{
	unsigned int minip = 0, maxip = 0;
	unsigned int octet = 0;
	unsigned int size = 0;	/* if using CIDR IP/mask format */
	unsigned int mask;
	char *p;
	enum iscan {
		I_BEG = 0,	/* beginning of line */
		I_IP1,		/* first octet*/
		I_IP1D,		/* dot after first octet */
		I_IP2,		/* second octet */
		I_IP2D,		/* dot after second octet */
		I_IP3,		/* third octet */
		I_IP3D,		/* dot after third octet */
		I_IP4,		/* fourth octet */
		I_MIP1,		/* first octet of max IP */
		I_MIP1D,	/* dot after first octet */
		I_MIP2,		/* second octet */
		I_MIP2D,	/* dot after second octet */
		I_MIP3,		/* third octet */
		I_MIP3D,	/* dot after third octet */
		I_MIP4,		/* fourth octet */
		I_PIP,		/* post first IP */
		I_MASK,		/* scanning a mask */
		I_PD		/* post dash */

	} state;
	state = I_BEG;
	for(p = (char *)line;;) {
		int ch = *p++;

		switch(state) {
			case I_BEG:
				if(isspace(ch))
					continue;
				if(isdigit(ch)) {	/* start a potential IP */
					octet = ch-'0';
					state = I_IP1;
					continue;
				}
				break;

			case I_IP1:	/* in an IP address */
			case I_IP2:
			case I_IP3:

			case I_MIP1:	/* in a second IP address */
			case I_MIP2:
			case I_MIP3:
				if(isdigit(ch)) {
					octet = octet*10 + ch-'0';
					continue;
				}
				if(ch == '.') {
					if(octet > 255) { /* not a real address */
						return 0;
					}
					maxip <<= 8;
					maxip += octet;
					state++;	/* corresponding dot state */
					continue;
				}
				/* otherwise, wasn't a full IP */
				return 0;

			case I_IP1D:	/* saw dot after an octet */
			case I_IP2D:
			case I_IP3D:

			case I_MIP1D:	/* saw dot after an octet */
			case I_MIP2D:
			case I_MIP3D:
				if(isdigit(ch)) {
					octet = ch-'0';
					state++;	/* next octet state */
					continue;
				}
				return 0;	/* wasn't an IP */

			case I_IP4:	/* in last octet */
				if(isdigit(ch)) {
					octet = octet*10 + ch-'0';
					continue;
				}

				/* OK, we have the IP */
				if(octet > 255) { /* not a real address */
					return 0;
				}
				maxip <<= 8;
				maxip += octet;
				minip = maxip;	/* until we see otherwise */
				if(!ch) break;	/* end of string */
				if(ch == '/')
					state = I_MASK;
				else if(ch == '-')
					state = I_PD;
				else
					state = I_PIP;
				continue;

			case I_MIP4:	/* in last octet of range max*/
				if(isdigit(ch)) {
					octet = octet*10 + ch-'0';
					continue;
				}

				/* OK, we have the IP */
				if(octet > 255) { /* not a real address */
					return 0;
				}
				maxip <<= 8;
				maxip += octet;
				if(ch && !isspace(ch))
					return 0;	/* junk at end */
				break;

			case I_PIP:
				if(ch == '/')
					state = I_MASK;
				else if(ch == '-')
					state = I_PD;
				else if(!ch)
					break;	/* single IP with spaces after it */
				else if(!isspace(ch))
					return 0;	/* junk */
				continue;
			case I_PD:
				if(isspace(ch))
					continue;
				if(!isdigit(ch))
					return 0;	/* junk */
				octet = ch-'0';
				state = I_MIP1;
				continue;
					
			case I_MASK:	/* CIDR mask size */
				if(isdigit(ch)) {
					size = size*10 + ch-'0';
					continue;
				}
				if(ch && !isspace(ch))
					return 0;	/* junk at end */
				if(size > 32)
					return 0;	/* not a reasonable cidr */
				mask = (1L<<(32-size))-1;
				if(maxip&mask && !sloppy)
					fprintf(stderr, "Invalid cidr: %s\n", line);
				minip &= ~mask;	/* force to CIDR boundary */
				maxip |= mask;
				
				break;
		}
		if(ch && !isspace(ch)) return 0;	/* crud at end of address */
		break;
	}
	/* got something, return it */
	spec->min = minip;
	spec->max = maxip;
#if DEBUG
	if(getenv("RANGES"))printf("range %08x - %08x\n", minip, maxip);
#endif /* DEBUG */
	if(minip > maxip)
		fprintf(stderr, "Backward range: %s\n", line);
	return 1;
}

/*
 * parse IPv6 address or CIDR
 * no ranges, since they don't seem popular
 * This should handle the full syntax in RFC 4291 sec 2.2 and 2.3 
 */
/* turn a hex digit to a value, has to be a hex digit */
#define xtod(c) ((c<='9')?(c-'0'):((c&15)+9))

int net_parse6(const char* line, struct netspec6* spec)
{
	v6addr ahi;	/* high part of address */
	v6addr alo;	/* low part of address */
	int nhi = 0;	/* how many bytes in ahi */
	int nlo = 0;	/* how many bytes in alo */
	int octet = -1;	/* current v4 octet, -1 means not an octet */
	unsigned int chunk = 0;	/* current 16 bit chunk */
	int size = -1;
	enum sv6 {
		V_BEG = 0,	/* beginning of string */
		V_HCH,		/* in a hi chunk */
		V_HC1,		/* hi, seen one colon */
		V_HC2,		/* hi, seen two colons */
		V_LCH,		/* in a low chunk */
		V_LC1,		/* seen a low colon */
		V_IC1,		/* seen initial colon */
		V_EIP1D,	/* dot after first octet of embedded IPv4 */
		V_EIP2,		/* second octet */
		V_EIP2D,	/* dot after second octet */
		V_EIP3,		/* third octet */
		V_EIP3D,	/* dot after third octet */
		V_EIP4,		/* fourth octet */
		V_SIZE		/* CIDR size */
	} state;
	char *p = (char *)line;
	
	state = 0;

	for(;;) {
		int ch = *p++;
		
		switch(state) {
			case V_BEG:
				if(isspace(ch)) continue;
				if(isxdigit(ch)) {	/* first chunk can't be v4 */
					chunk = xtod(ch);
					state = V_HCH;
					continue;
				}
				if(ch == ':') {
					state = V_IC1;
					continue;
				}
				return 0;	/* not an IP */

			case V_IC1:		/* leading colon must be two colons */
				if(ch == ':') {
					state = V_HC2;
					continue;
				}
				return 0;	/* not an IP */

			case V_HCH:
				if(isxdigit(ch)) {
					chunk = (chunk<<4)+xtod(ch);
					if(isdigit(ch)) {
						if(octet >= 0) octet = octet*10 + ch-'1';
					} else
						octet = -1; /* not v4 */
					continue;
				}
				/* finish the current chunk */

				if(ch == '.') {
					if(nhi == 12 && octet >= 0 && octet <= 255) { /* embedded v4 */
						ahi.a[nhi++] = octet;
						state = V_EIP1D;
						continue;
					}
					return 0;	/* not an IP */
				}

				if(nhi > 14) return 0;	/* too many chunks */
				ahi.a[nhi++] = chunk >> 8;	/* big-endian for memcmp() */
				ahi.a[nhi++] = chunk & 255;
				if(ch == ':') {
					state = V_HC1;
					continue;
				}
				if(ch == '/') {
					state = V_SIZE;
					continue;
				}
				break;	/* end of the number */

			case V_HC1:
				if(isxdigit(ch)) {
					chunk = xtod(ch);
					if(isdigit(ch))
						octet = chunk;
					else
						octet = -1;
					state = V_HCH;
					continue;
				}
				if(ch == ':') {
					state = V_HC2;
					continue;
				}
				return 0;	/* not an IP */
				
			case V_HC2:
				if(isxdigit(ch)) {	/* two colons and digit, start low half */
					chunk = xtod(ch);
					if(isdigit(ch))
						octet = chunk;
					else
						octet = -1;
					state = V_LCH;
					continue;
				}
				if(ch == '/') {
					state = V_SIZE;
					continue;
				}
				break;	/* end of only high half */

			case V_LCH:
				if(isxdigit(ch)) {
					chunk = (chunk<<4)+xtod(ch);
					if(isdigit(ch)) {
						if(octet >= 0) octet = octet*10 + ch-'0';
					} else
						octet = -1; /* not v4 */
					continue;
				}
				/* finish the current chunk */
				if(ch == '.') {
					if((nhi+nlo) < 12
					   && octet >= 0 && octet <= 255) { /* embedded v4 */
						/* move all into ahi */
						memset(ahi.a+nhi, 0, 12-(nhi+nlo));
						if(nlo) {
							memcpy(ahi.a+12-nlo, alo.a, nlo);
							nlo = 0;
						}
						nhi = 12;
						ahi.a[nhi++] = octet;
						state = V_EIP1D;
						continue;
					}
					return 0;	/* not an embedded v4 */
				}

				if((nhi+nlo) > 12) return 0;	/* too many chunks */
				if(chunk > 0xffff) return 0;	/* too big for a chunk */
				alo.a[nlo++] = chunk >> 8;	/* big-endian for memcmp() */
				alo.a[nlo++] = chunk & 255;
				if(ch == ':') {
					state = V_LC1;
					continue;
				}
				if(ch == '/') {
					state = V_SIZE;
					continue;
				}
				break;	/* end of the number */
				
			case V_LC1:
				if(isxdigit(ch)) {
					chunk = xtod(ch);
					if(isdigit(ch))
						octet = chunk;
					else
						octet = -1;
					state = V_LCH;
					continue;
				}
				return 0;	/* trailing junk, not an IP */

			case V_EIP1D:		/* dot after first octet of embedded IPv4 */
			case V_EIP2D:		/* dot after second octet */
			case V_EIP3D:		/* dot after third octet */
				if(isdigit(ch)) {
					octet = ch-'0';
					state++;
					continue;
				}
				return 0;	/* not an IP */

			case V_EIP2:		/* second octet */
			case V_EIP3:		/* third octet */
				if(isdigit(ch)) {
					octet = octet*10 + ch-'0';
					continue;
				}
				if(ch == '.') {
					if(octet > 255) return 0;	/* not an IP */
					ahi.a[nhi++] = octet;
					state++;
					continue;
				}
				return 0;	/* not an IP */

			case V_EIP4:		/* fourth octet */
				if(isdigit(ch)) {
					octet = octet*10 + ch-'0';
					continue;
				}
				if(octet > 255) break;	/* not an IP */
				ahi.a[nhi++] = octet;
				if(ch == '/') {
					state = V_SIZE;
					continue;
				}
				break;	/* four octets, we're done */

			case V_SIZE:
				if(isdigit(ch)) {
					if (size < 0) size = 0;
					size = size*10 + ch-'0';
					continue;
				}
				if(size < 0 || size > 128) return 0;	/* no digits or junk at the end */
				break;
		}
		break;
		/* accept if \0 or space after an item */
		if(ch && !isspace(ch)) return 0;	/* crud in the item */
	}

	/* combine ahi and alo */
	if(nlo && (nhi+nlo) >= 16) return 0;	/* too many chunks */
	if((nhi+nlo) < 16) 
		memset(ahi.a+nhi, 0, 16-(nhi+nlo));
	if(nlo)memcpy(ahi.a+16-nlo, alo.a, nlo);
	if (!applymask6(ahi, size, spec) && !sloppy) {
		p = strchr(line, '\n');
		if(p) *p = 0;	/* just a string */
			fprintf(stderr, "Bad cidr range: %s\n", line);
	}
	return 1;
}

/* Return 0 (softfail) if bits were set in host part of CIDR address */
static int applymask6(const v6addr ahi, int size, struct netspec6 *spec)
{
	int badbits = 0;	/* bits already set, bad CIDR */
	assert(size >= 0 && size <= 128);

	spec->min = spec->max = ahi;

	if(size >= 0) {	/* set low bits for the range */
			/* and also check that they were already zero */
		int nbits = size&7; /* bits within a byte */
		int nbytes = size >> 3;

		if(nbits) {
			int mask = 255>>nbits;	

			if(ahi.a[nbytes]&mask) badbits = 1;
			spec->min.a[nbytes] &= 255-mask;
			spec->max.a[nbytes] |= mask;
			nbytes++;
		}
		while(nbytes < 16) {
			if(ahi.a[nbytes]) badbits = 1;
			spec->min.a[nbytes] = 0;
			spec->max.a[nbytes] = 255;
			nbytes++;
		}
	}
	return !badbits;
}

/* Compare two netspecs, for sorting. Comparison is done on minimum of range */
int netsort(const void* a, const void* b)
{
	unsigned int c1 = ((struct netspec*)a)->min;
	unsigned int c2 = ((struct netspec*)b)->min;
	if (c1 < c2) return -1;
	if (c1 > c2) return +1;

	c1 = ((struct netspec*)a)->max;
	c2 = ((struct netspec*)b)->max;
	if (c1 < c2) return -1;
	if (c1 > c2) return +1;
	return 0;
}

int netsort6(const void* a, const void* b)
{
	int r;
	v6addr *c1 = &((struct netspec6*)a)->min;
	v6addr *c2 = &((struct netspec6*)b)->min;
	r = v6cmp(*c1, *c2);
	if(r != 0) return r;

	c1 = &((struct netspec6*)a)->max;
	c2 = &((struct netspec6*)b)->max;
	return v6cmp(*c1, *c2);
}

int main(int argc, char* argv[])
{
	static char shortopts[] = "acCDe:f:iqsvV";
	char* pat_filename = NULL;		/* filename containing patterns */
	char* pat_strings = NULL;		/* pattern strings on command line */
	int foundopt;

	if (argc == 1)
	{
		fprintf(stderr, TXT_USAGE);
		return EXIT_ERROR;
	}

	while ((foundopt = getopt(argc, argv, shortopts)) != -1)
	{
		switch (foundopt)
		{
			case 'V':
				puts(TXT_VERSION);
				return EXIT_ERROR;
				
			case 'c':
				counting = 1;
				break;
				
			case 'v':
				invert = 1;
				break;
				
			case 'h':
				nonames = 1;
				break;

			case 'a':
				anchor = 1;
				break;

			case 'i':
				igbadpat = 1;
				break;

			case 'q':
				quick = 1;
				break;

			case 's':
				sloppy = 1;
				break;

			case 'D':
				didrsearch = 1;
				/* fall through */

			case 'C':
				cidrsearch = 1;
				break;

			case 'e':
				pat_strings = optarg;
				break;

			case 'f':
				pat_filename = optarg;
				break;
				
			default:
				fprintf(stderr, TXT_USAGE);
				return EXIT_ERROR;
		}
	}
	if (!pat_filename && !pat_strings)
	{
		if (optind < argc)
			pat_strings = argv[optind++];
		else
		{
			fprintf(stderr, "Specify PATTERN or -f FILE to read patterns from\n");
			return EXIT_ERROR;
		}
	}
	
	/* Load patterns defining networks */
	if (pat_filename)
	{
		FILE* data = fopen(pat_filename, "r");
		if (data)
		{
			while (getline(&linep, &linesize, data) > 0)
			{
				if (*linep != '#') {
					if(strchr(linep, ':')) {
						struct netspec6 spec6;

						if(net_parse6(linep, &spec6))
							array_insert6(&spec6);
						else if(!igbadpat)
							fprintf(stderr, "Not a pattern: %s", linep);
					} else {
						struct netspec spec;

						if (net_parse(linep, &spec))
							array_insert(&spec);
						else if(!igbadpat)
							fprintf(stderr, "Not a pattern: %s", linep);
					}
				}
			}
			fclose(data);
		}
		else
		{
			perror(pat_filename);
			return EXIT_ERROR;
		}
	}
	if (pat_strings)
	{
		char* token = strtok(pat_strings, TOKEN_SEPS);
		while (token)
		{
			if(strchr(token, ':')) {
				struct netspec6 spec6;

				if(net_parse6(token, &spec6))
					array_insert6(&spec6);
				else if(!igbadpat)
					fprintf(stderr, "Not a pattern: %s\n", token);
			} else {
				struct netspec spec;

				if (net_parse(token, &spec))
					array_insert(&spec);
				else if(!igbadpat)
					fprintf(stderr, "Not a pattern: %s\n", token);
			}
			token = strtok(NULL, TOKEN_SEPS);
		}
	}
	
	if(!npatterns && !n6patterns) {
		fprintf(stderr, "No patterns to match\n");
		return EXIT_ERROR;
	}

	/* Prepare array for rapid searching */
	if(npatterns) {
		struct netspec *inp, *outp;
#if DEBUG
		char *dnp;
		if((dnp = getenv("PRESORT4")) != 0) {
			FILE *f = fopen(dnp, "w");
			struct netspec *p;
			for(p = array; p < array+npatterns; p++)
				fprintf(f, "%d.%d.%d.%d-%d.%d.%d.%d\n", p->min>>24,
					  (p->min>>16)&255, (p->min>>8)&255, p->min&255,
					  p->max>>24, (p->max>>16)&255, (p->max>>8)&255, p->max&255);
			fclose(f);
		}
#endif /* DEBUG */		
		qsort(array, npatterns, sizeof(struct netspec), netsort);
#if DEBUG
		if((dnp = getenv("POSTSORT4")) != 0) {
			FILE *f = fopen(dnp, "w");
			struct netspec *p;
			for(p = array; p < array+npatterns; p++)
				fprintf(f, "%d.%d.%d.%d-%d.%d.%d.%d\n", p->min>>24,
					  (p->min>>16)&255, (p->min>>8)&255, p->min&255,
					  p->max>>24, (p->max>>16)&255, (p->max>>8)&255, p->max&255);
			fclose(f);
		}
#endif /* DEBUG */		

		/* combine overlapping ranges
		 * outp is clean so far, inp is checked for overlap
		 */
		outp = array;
		for (inp = array+1; inp < array+npatterns; inp++)
		{
			if (inp->max <= outp->max)
				continue;		/* contained within previous range, ignore */

			if(inp->min <= outp->max) {	/* overlapping ranges, combine */
				outp->max = inp->max;
				continue;
			}
			if(++outp < inp)
				*outp = *inp;		/* move down due to previously combined or ignored */
		}
		npatterns = outp-array+1;		/* adjusted count after combinations */
#if DEBUG
		if((dnp = getenv("POSTMERGE4")) != 0) {
			FILE *f = fopen(dnp, "w");
			struct netspec *p;
			for(p = array; p < array+npatterns; p++)
				fprintf(f, "%d.%d.%d.%d-%d.%d.%d.%d\n", p->min>>24,
					  (p->min>>16)&255, (p->min>>8)&255, p->min&255,
					  p->max>>24, (p->max>>16)&255, (p->max>>8)&255, p->max&255);
			fclose(f);
		}
#endif /* DEBUG */		
	}
	if(n6patterns) {
		struct netspec6 *inp, *outp;

		qsort(array6, n6patterns, sizeof(struct netspec6), netsort6);

		/* combine overlapping ranges
		 * outp is clean so far, inp is checked for overlap
		 */
		outp = array6;
		for (inp = array6+1; inp < array6+n6patterns; inp++)
		{
			if (v6cmp(inp->max, outp->max) <= 0)
				continue;		/* contained within previous range, ignore */

			if(v6cmp(inp->min, outp->max)<=0) {	/* overlapping ranges, combine */
				outp->max = inp->max;
				continue;
			}
			if(++outp < inp)
				*outp = *inp;		/* move down due to previously combined or ignored */
		}
		n6patterns = outp-array6+1;		/* adjusted count after combinations */
	}

# if DEBUG
	{	/* DEBUG */
		int i,n;
		for(n = 0; n < n6patterns; n++) {
			printf("min %d:", n);
			for(i = 0; i<16; i++) printf(" %02x", array6[n].min.a[i]);
			printf("\nmax %d:",n);
			for(i = 0; i<16; i++) printf(" %02x", array6[n].max.a[i]);
			printf("\n");
		}
	}
# endif /* DEBUG */
	if (optind >= argc) {
		scan_read(stdin, NULL);
	} else {
		if(optind+1 >= argc) nonames = 1;	/* just one file, no name */

		while(optind < argc) {
			char *fn = argv[optind++];
			FILE *f = fopen(fn, "r");
			char *fmap;
			size_t flen;
			struct stat statbuf;
		
			if(!f) {
				perror(fn);
				return EXIT_ERROR;
			}
			if(fstat(fileno(f), &statbuf) != 0 || (statbuf.st_mode&S_IFMT)!= S_IFREG ) {
				scan_read(f, fn);		/* can't stat or not a normal file, fall back to read */
				fclose(f);
				continue;
			}
			flen = statbuf.st_size;
			if(flen == 0) {
				fclose(f);	/* empty file, forget it */
				continue;
			}

			fmap = mmap(NULL, flen, PROT_READ, MAP_SHARED, fileno(f), (off_t)0);
			if(fmap == MAP_FAILED) {
				perror("map failed");
				scan_read(f, fn);	/* can't map, fall back to read */
				fclose(f);
				continue;
			}

			scan_block(fmap, flen, fn);
			munmap(fmap, flen);
			fclose(f);
		}
	}

	/* Cleanup */
	if (counting)
		printf("%u\n", nmatch);
	if (nmatch)
		return EXIT_OK;
	else
		return EXIT_NOMATCH;
}

/* scan a line at a time */
static void scan_read(FILE *f, const char *fn)
{
	ssize_t len;

	while((len = getline(&linep, &linesize, f)) > 0)
	      scan_block(linep, len, fn);
}

static int netmatch(const struct netspec ip4);
static int netmatch6(const struct netspec6 ip6);

/* scan some text, must be whole lines
 * generally either one line or the whole file
 * bp: pointer to buffer
 * blen: length of buffer
 * fn: filename for printing
 * This should handle the full V6 syntax in RFC 4291 sec 2.2 and 2.3 except for
 * :: for a zero address
 * strings of colons may confuse it
 */
static void scan_block(char *bp, size_t blen, const char *fn)
{
	enum sscan {
		S_BEG = 0,	/* beginning of line */
		S_SC,		/* scan for IP */
		S_NSC,		/* saw a dot, scan for non-digit */
		S_IP1,		/* first octet or maybe first v6 chunk*/
		S_IP1D,		/* dot after first octet */
		S_IP2,		/* second octet */
		S_IP2D,		/* dot after second octet */
		S_IP3,		/* third octet */
		S_IP3D,		/* dot after third octet */
		S_IP4,		/* fourth octet */
		S_V4SZ,		/* v4 cidr prefix */
		S_HCH,		/* in a hi v6 chunk */
		S_HC1,		/* hi, seen one colon */
		S_HC2,		/* hi, seen two colons */
		S_LCH,		/* in a low chunk */
		S_LC1,		/* seen a low colon */
		S_IC1,		/* seen initial colon */
		S_EIP1D,	/* dot after first octet in embedded v4 */
		S_EIP2,		/* second octet */
		S_EIP2D,	/* dot after second octet */
		S_EIP3,		/* third octet */
		S_EIP3D,	/* dot after third octet */
		S_EIP4,		/* fourth octet */
		S_V6SZ,		/* v6 cidr prefix */
		S_SCNL,		/* scan for new line */
		S_SCNLP		/* scan for new line and print line */
	} state;
	enum sscan snext = anchor?S_SCNL:S_SC;	/* state after not an IP */

	char *p = bp;		/* current character */
	char *plim = bp+blen;	/* end of buffer */
	char *lp = bp;		/* beginning of current line */
	unsigned int ip4 = 0;	/* IPv4 value */
	int octet = 0;		/* current octet */
	int size = -1;		/* CIDR size */
	v6addr ahi;		/* high part of address */
	v6addr alo;		/* low part of address */
	struct netspec range4;  /* IPv4 address or range */
	struct netspec6 range6; /* IPv6 address or range */
	int nhi = 0;		/* how many bytes in ahi */
	int nlo = 0;		/* how many bytes in alo */
	unsigned int chunk = 0;	/* current 16 bit chunk */
	int seenone = 0;	/* seen an address on this line, for -v */

	state = S_BEG;
	for(p = bp; p < plim;) {
		int ch = *p++;

		switch(state) {
			case S_BEG:	/* beginning of line */
				lp = p-1;
				seenone = 0;
				/* skip leading spaces */
				while(p < plim && (ch == ' ' || ch == '\t'))
					ch = *p++;
				/* fall through */

			case S_SC:		/* normal scanning */
				if(isdigit(ch)) {	/* start a potential IP of either type */
					ip4 = 0;
					state = S_IP1;
					nhi = nlo = 0;
					octet = chunk = ch-'0';
					continue;
				} else if(isxdigit(ch)) {
					state = S_HCH;
					nhi = nlo = 0;
					octet = -1;	/* hex, not v4 */
					chunk = xtod(ch);
					continue;
				} else if(ch == ':') {
					state = S_IC1;
					continue;
				} else if(quick && ch == '.') {
					state = S_NSC;
					continue;
				}
				break;

			case S_NSC:		/* ignore crud after a dot */
				if(isdigit(ch) || ch == '.')
					continue;
				state = S_SC;
				break;

			case S_IC1:		/* initial colon must be two colons and lo part */
				if(ch == ':') {
					nhi = nlo = 0;
					state = S_HC2;
					continue;
				}
				/* rescan as normal in case it was
				 * a random colon before an IP
				 */
				state = S_SC;
				p--;
				continue;

			case S_HCH:	/* high v6 chunk */
				if(isxdigit(ch)) {
					chunk = (chunk<<4) + xtod(ch);
					if(isdigit(ch))
						octet = octet*10 + ch-'0';	/* in case it turns out to be v4 */
					else
						octet = -1;			/* hex, can't be v4 */
					continue;
				}
				/* finish the current chunk */
				if(ch == '.' && nhi < 14 && octet >= 0) { /* possible v4 address, is it embedded? */
					if(octet > 255) { /* not a real address */
						break;
					}
					/* is it embedded? */
					if(nhi == 12) {
						ahi.a[nhi++] = octet;
						state = S_EIP1D;
						continue;
					}
					/* v6 address was too short,
					 * must be a regular v4 address
					 */
					ip4 = octet;
					state = S_IP1D;	/* corresponding dot state */
					continue;
				}
				if(chunk > 0xffff)
					break;		/* value too big */
				if(nhi < 16) {	/* if too long, keep parsing to avoid strange matches */
					ahi.a[nhi++] = chunk >> 8;	/* big-endian for memcmp() */
					ahi.a[nhi++] = chunk & 255;
				}
				if(ch == ':') {
					state = S_HC1;
					continue;
				}
				/* was it full address? */
				if(nhi == 16) {
					if(!n6patterns) break;	/* no v6 patterns */
					if(cidrsearch && ch == '/') {
						size = 0;
						state = S_V6SZ;
						continue;
					}
					seenone = 1;
					range6.min = range6.max = ahi;
					if(!netmatch6(range6))
						break; /* didn't match */
					state = S_SCNLP;
					goto scnlp;	/* in case it was a \n */
				}
				break;	/* partial address, not an IP */

			case S_HC1:	/* colon separator in hi part */
				if(isxdigit(ch)) {
					chunk = xtod(ch);
					if(isdigit(ch))
						octet = ch-'0';
					else
						octet = -1;
					state = S_HCH;
					continue;
				}
				if(ch == ':') {	/* two colons, might be end or lo part can follow */
					state = S_HC2;
					continue;
				}
				break;	/* not an IP */

			case S_HC2:	/* seen high:: might be end or might be low chunk */
				if(isxdigit(ch)) {	/* two colons and digit, start low chunks */
					chunk = xtod(ch);
					if(isdigit(ch))
						octet = chunk;
					else
						octet = -1;
					state = S_LCH;
					continue;
				}

				/* high part only, check it */
				if(!nhi) {
					if(ch == ':')	/* string of possibly leading colons */
						continue;
					break;	/* don't match :: as zero address */
				}
				if(!n6patterns) break;	/* no v6 patterns */
				memset(ahi.a+nhi, 0, 16-nhi);	/* zero low bytes */
				if(cidrsearch && ch == '/') {
					size = 0;
					state = S_V6SZ;
					continue;
				} else
					size = -1;

				seenone = 1;
				range6.min = range6.max = ahi;
				if(!netmatch6(range6))
					break; /* didn't match */
				state = S_SCNLP;
				goto scnlp;	/* in case it was a \n */

			case S_V6SZ:
				if(isdigit(ch)) {
					if (size >= 0)
						size = size*10 + ch-'0';
					if(size > 128) /* gobble up the rest */
						size = -1;
					continue;
				}
				if(!n6patterns) break;	/* no v6 patterns */
				seenone = 1;
				if (size < 0) size = 0; /* ignore bad prefix */
				/* TODO: check badbits? naah */
				applymask6(ahi, size, &range6);
				if(!netmatch6(range6))
					break; /* didn't match */
				state = S_SCNLP;
				goto scnlp;	/* in case it was a \n */

			case S_LCH:		/* low chunk */
				if(isxdigit(ch)) {
					chunk = (chunk<<4)+xtod(ch);
					if(isdigit(ch))
						octet = octet*10 + ch-'0';	/* in case it turns out to be v4 */
					else
						octet = -1;
					continue;
				}
				/* finish the current chunk */
				if(ch == '.' && octet >= 0 && octet <= 255) { /* maybe a v4 address */
					if((nhi+nlo) < 12) { /* embedded v4 */
						/* move all into ahi */
						memset(ahi.a+nhi, 0, 12-(nhi+nlo));
						if(nlo)
							memcpy(ahi.a+12-nlo, alo.a, nlo);
						nhi = 12;
						ahi.a[nhi++] = octet;
						state = S_EIP1D;
						continue;
					}
				}
				/* doesn't look like an octet, or too
				 * long to be embedded, treat as
				 * likely v6
				 */
				if(chunk > 0xffff) break;	/* too big for a chunk */
				if(nlo < 16) {	/* keep parsing overlong to avoid strange results */
					alo.a[nlo++] = chunk >> 8;	/* big-endian for memcmp() */
					alo.a[nlo++] = chunk & 255;
				}
				if(ch == ':') {
					state = S_LC1;
					continue;
				}
				/* end of lo part, check it */
				if(!n6patterns) break;		/* no v6 patterns */
				if((nhi+nlo) >= 14) break;	/* too many chunks. not an IP */
				memset(ahi.a+nhi, 0, 16-(nhi+nlo));	/* combine hi and lo parts */
				memcpy(ahi.a+(16-nlo), alo.a, nlo);
				if(cidrsearch && ch == '/') {
					state = S_V6SZ;
					size = 0;
					continue;
				}
				seenone = 1;
				range6.min = range6.max = ahi;
				if(!netmatch6(range6))
					break; /* didn't match */
				state = S_SCNLP;
				goto scnlp;	/* in case it was a \n */

			case S_LC1:	/* seen a colon after a low chunk */
				if(isxdigit(ch)) {
					chunk = xtod(ch);
					if(isdigit(ch))
						octet = chunk;
					else
						octet = -1;
					state = S_LCH;
					continue;
				}
				break;	/* trailing junk, not an IP */

			case S_IP1:	/* in an IP address, don't know yet which kind */
				if(isxdigit(ch)) {
					chunk = (chunk<<4) + xtod(ch);
					if(!isdigit(ch)) {
						state = S_HCH;	/* doesn't look like a v4 address */
						octet = -1;
						continue;
					}
				} else if(ch == ':') {
					/* finish the current chunk,
					 * which must be chunk 0 */
					ahi.a[nhi++] = chunk >> 8;	/* big-endian for memcmp() */
					ahi.a[nhi++] = chunk & 255;
					state = S_HC1;
					continue;
				}
				/* fall through */
			case S_IP2:
			case S_IP3:
				if(isdigit(ch)) {
					octet = octet*10 + ch-'0';
					continue;
				}
				if(ch == '.') {
					if(octet > 255) { /* not a real address */
						break;
					}
					ip4 <<= 8;
					ip4 += octet;
					state++;	/* corresponding dot state */
					continue;
				}
				/* otherwise, wasn't a full IP */
				break;

			case S_IP1D:	/* saw dot after an octet */
			case S_IP2D:
			case S_IP3D:
			case S_EIP1D:	/* saw dot after an embedded octet */
			case S_EIP2D:
			case S_EIP3D:
				if(isdigit(ch)) {
					octet = ch-'0';
					state++;	/* next digit state */
					continue;
				}
				break;	/* wasn't an IP */

			case S_IP4:	/* in last octet */
				if(isdigit(ch)) {
					octet = octet*10 + ch-'0';
					continue;
				}
				/* OK, we have the IP */
				if(quick && ch == '.') {	/* seen crud, skip it */
					state = S_NSC;
					continue;
				}
				if(octet > 255) { /* not a real address */
					break;
				}
				ip4 <<= 8;
				ip4 += octet;
				if(!npatterns) break; /* no v4 patterns */
				if(cidrsearch && ch == '/') {
					state = S_V4SZ;
					size = 0;
					continue;
				}
				seenone = 1;
				range4.min = range4.max = ip4;
				if(!netmatch(range4))
					break; /* didn't match */
				state = S_SCNLP;
				goto scnlp;	/* in case it was a \n */

                        case S_V4SZ:    /* cidr size */
				if(isdigit(ch)) {
					if (size >= 0)
						size = size*10 + ch-'0';
					if(size > 32) /* gobble up the rest */
						size = -1;
					continue;
				}
				seenone = 1;
				range4.min = range4.max = ip4;
				if(size >= 0) {		/* ignore bad prefix */
					int mask = (1L<<(32-size))-1;
					range4.min &= ~mask; /* force to CIDR boundary */
					range4.max |= mask;
				}
				if(!netmatch(range4))
					break; /* didn't match */
				state = S_SCNLP;
				goto scnlp;	/* in case it was a \n */
				
			case S_EIP2:	/* in embedded octet */
			case S_EIP3:
				if(isdigit(ch)) {
					octet = octet*10 + ch-'0';
					continue;
				}
				if(ch == '.') {
					if(octet > 255) { /* not a real address */
						break;
					}
					ahi.a[nhi++] = octet;
					state++;	/* corresponding dot state */
					continue;
				}
				/* otherwise, wasn't a full IP */
				break;

			case S_EIP4:	/* in last embedded octet */
				if(isdigit(ch)) {
					octet = octet*10 + ch-'0';
					continue;
				}
				/* OK, we have the IP */
				if(quick && ch == '.') {	/* seen crud, skip it */
					state = S_NSC;
					continue;
				}
				if(octet > 255) { /* not a real address */
					break;
				}
                                /* no CIDR allowed with IPv4 embedded in IPv6 */
				ahi.a[nhi++] = octet;
				seenone = 1;
				if(n6patterns) {
					range6.min = range6.max = ahi;
					if(netmatch6(range6)) {	/* try a v6 pattern */
						state = S_SCNLP;
						goto scnlp;	/* in case it was a \n */
					}
				}
				/* get the v4 address as an int and try
				 * that */
				ip4 = (ahi.a[12]<<24)|(ahi.a[13]<<16)|(ahi.a[14]<<8)|ahi.a[15];
				if(cidrsearch && ch == '/') {
					state = S_V4SZ;
					size = 0;
					continue;
				}
				range4.min = range4.max = ip4;
				if(!npatterns || !netmatch(range4))
					break; /* didn't match */

				state = S_SCNLP;
				/* fall through, in case it was a \n */

scnlp:
			case S_SCNLP:	/* print this line */
				/* HACK scan the rest of the line fast */
				while(ch != '\n' && p < plim)
					ch = *p++;

				if(ch == '\n') {
					if(!invert) {
						nmatch++;
						if(!counting) {
							if(fn && !nonames)
								printf("%s:", fn);
							fwrite(lp, 1, p-lp, stdout);
						}
					}
					state = S_BEG;
				}
				continue;

			case S_SCNL:
				/* HACK scan the rest of the line fast */
				while(ch != '\n' && p < plim)
					ch = *p++;
				break;
		}
		/* default action if it wasn't an IP */
		if(ch == '\n') {
			if(invert && seenone) {	/* -v prints or counts lines with IPs that didn't match */
				nmatch++;
				if(!counting) {
					if(fn && !nonames)
						printf("%s:", fn);
					fwrite(lp, 1, p-lp, stdout);
				}
			}
			state = S_BEG;
		} else
			state = snext;
		continue;

	}
} /* scan_block */

/*
 * binary range search for a value
 */
static int
netmatch(const struct netspec ip4)
{
	int minx = 0;
	int maxx = npatterns-1;
	int tryx = 0;

# if DEBUG
	{	/* DEBUG */

		assert(npatterns);	/* don't call this if there are no v4 patterns */
		printf("match: %x %d.%d.%d.%d-%x %d.%d.%d.%d\n", ip4.min, ip4.min>>24,
		       (ip4.min>>16)&255, (ip4.min>>8)&255, ip4.min&255,
		       ip4.max, ip4.max>>24, (ip4.max>>16)&255, (ip4.max>>8)&255, ip4.max&255);
	}
# endif
	/* make sure it's in range */
	if(ip4.max < array[0].min || ip4.min > array[maxx].max) return 0;

	while(minx <= maxx) {
		tryx = (minx+maxx)/2;
# if DEBUG
		if(getenv("TRY")) printf("try %d:%d -> %d %x %x\n", minx, maxx, tryx, array[tryx].min, array[tryx].max);
# endif

		if(ip4.max < array[tryx].min) {
			maxx = tryx-1;
			continue;
		}
		if(ip4.min > array[tryx].max) {
			minx = tryx+1;
			continue;
		}
		break;	/* gee, we may have found it */
	}

	if(ip4.min >= array[tryx].min && ip4.max <= array[tryx].max) return 1; /* target in pattern */
	if(didrsearch) {	/* look for overlap */
		if(ip4.min <= array[tryx].min && ip4.max >= array[tryx].max) return 1; /* pattern in target */
		if(ip4.min >= array[tryx].min && ip4.min <= array[tryx].max) return 1; /* base of target in pattern */
		if(ip4.max >= array[tryx].min && ip4.max <= array[tryx].max) return 1; /* end of target in pattern */
	}
	return 0;	/* not in the current entry */
}

static int
netmatch6(const struct netspec6 ip6)
{
	int minx = 0;
	int maxx = n6patterns-1;
	int tryx = 0;

# if DEBUG
	{	/* DEBUG */
		int i;

		assert(n6patterns);	/* don't call this if there are no v6 patterns */
		printf("match:");
		for(i = 0; i<16; i++) printf(" %02x", ip6.min.a[i]);
		printf("-");
		for(i = 0; i<16; i++) printf(" %02x", ip6.max.a[i]);
		printf("\n");
	}
# endif
	/* make sure it's in range */
	if(v6cmp(ip6.max, array6[0].min) < 0 || v6cmp(ip6.min, array6[maxx].max) > 0) return 0;

	while(minx <= maxx) {
		tryx = (minx+maxx)/2;

		if(v6cmp(ip6.min, array6[tryx].min)<0) {
			maxx = tryx-1;
			continue;
		}
		if(v6cmp(ip6.min, array6[tryx].max)>0) {
			minx = tryx+1;
			continue;
		}
		break; /* gee, we may have found it */
	}

# if DEBUG
	{	/* DEBUG */
		int i;

		assert(n6patterns);	/* don't call this if there are no v6 patterns */
		printf("candidate: %d/%d", minx, maxx);
		for(i = 0; i<16; i++) printf(" %02x", array6[minx].min.a[i]);
		printf("-");
		for(i = 0; i<16; i++) printf(" %02x", array6[minx].max.a[i]);
		printf("\n");
	}
# endif

	if(v6cmp(ip6.min, array6[tryx].min) >= 0 && v6cmp(ip6.max, array6[tryx].max) <= 0) return 1; /* target in pattern */
	if(didrsearch) {
		if(v6cmp(ip6.min, array6[tryx].min) <= 0 && v6cmp(ip6.max, array6[tryx].max) >= 0) return 1; /* pattern in target */
		if(v6cmp(ip6.min, array6[tryx].min) >= 0 && v6cmp(ip6.min, array6[tryx].max) <= 0) return 1; /* base in pattern */
		if(v6cmp(ip6.max, array6[tryx].min) >= 0 && v6cmp(ip6.max, array6[tryx].max) <= 0) return 1; /* end in target */
	}
	return 0;	/* not in the current entry */
}
