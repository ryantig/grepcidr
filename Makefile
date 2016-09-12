#
# Makefile for grepcidr
#

# Set to where you'd like grepcidr installed
INSTALLDIR=/usr/local/bin

# Set to your favorite C compiler and flags
# with GCC, -O3 makes a lot of difference
# -DDEBUG=1 prints out hex versions of IPs and matches

CFLAGS=-O3 -Wall -pedantic
#CFLAGS=-g -Wall -pedantic -DDEBUG=1
TFILES=COPYING ChangeLog Makefile README grepcidr.1 grepcidr.c
DIR!=basename ${PWD}

# End of settable values

all:	grepcidr

grepcidr:	grepcidr.c
	$(CC) $(CFLAGS) -o grepcidr grepcidr.c

install:	grepcidr
	cp grepcidr $(INSTALLDIR)

clean:
	rm -f grepcidr

tar:
	cd ..; tar cvjf ${DIR}.tjz ${TFILES:C%^%${DIR}/%}
