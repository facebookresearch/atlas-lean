# Actions of x86-TSO events

The action of an event reads a value $v$ at a location $l$,
writes $v$ at $l$, or is an MFENCE (Owens, Sarkar and Sewell, *TPHOLs 2009*, Section 3). The
source's actions also include LFENCE and SFENCE barriers, which are left out, as no condition of
validity uses them.
