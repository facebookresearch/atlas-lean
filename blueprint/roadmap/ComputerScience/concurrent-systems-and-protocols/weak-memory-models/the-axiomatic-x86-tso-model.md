# The axiomatic x86-TSO model

In the axiomatic x86-TSO model, a program's execution is abstracted as a set of events: memory reads and writes of particular values at particular locations, register reads and writes, and MFENCE events, with each event belonging to an instruction of a processor, a program order $\mathrm{po}$ on the events of each processor (including the causality order among the events of one instruction), and a set of groups of events, one for each LOCK'd instruction. An *execution witness* consists of a *memory order* $\mathrm{mo}$, a partial order on the memory accesses that is a linear order on the memory writes; a *reads-from map* $\mathrm{rf}$ relating each read to a write of the same location and value; and an initial state, a partial map from locations to values. The witness is *valid* if the following hold.

- Every memory read $r$ with $(w, r) \in \mathrm{rf}$ reads from a write $w$ that is $\mathrm{mo}$-maximal among the writes to the location of $r$ that precede $r$ in $\mathrm{mo}$ or in $\mathrm{po}$; a read outside the range of $\mathrm{rf}$ takes the initial value of its location, and no write to that location precedes it in $\mathrm{mo}$ or in $\mathrm{po}$.
- $\mathrm{po}$ is included in $\mathrm{mo}$ for a memory read followed by any memory access, for a memory write followed by a memory write, for a memory write followed by a memory read with an MFENCE between them, and for any two memory accesses one of which belongs to a LOCK'd instruction.
- The memory accesses of each LOCK'd instruction are atomic in $\mathrm{mo}$: every other memory access precedes all of them or follows all of them.
- Every prefix of $\mathrm{mo}$ is finite, and for every write $w$ only finitely many reads of its location are unrelated to $w$ by $\mathrm{mo}$.

In particular, a memory write followed in program order by a read of the same location need not precede it in $\mathrm{mo}$; the first condition still makes the read see that write or a later one.

## Sources

- S. Owens, S. Sarkar and P. Sewell, "A better x86 memory model: x86-TSO", *TPHOLs 2009*, LNCS 5674, Springer, 2009, Section 3.2
- P. Sewell, S. Sarkar, S. Owens, F. Zappa Nardelli and M. O. Myreen, "x86-TSO: a rigorous and usable programmer's model for x86 multiprocessors", *Communications of the ACM* 53(7):89–97, 2010
