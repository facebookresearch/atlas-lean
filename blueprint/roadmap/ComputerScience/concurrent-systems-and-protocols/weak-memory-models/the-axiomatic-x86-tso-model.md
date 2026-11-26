# The axiomatic x86-TSO model

In the axiomatic x86-TSO model, a program's execution is abstracted as a set of events: memory reads and writes of particular values at particular addresses, register reads and writes, and MFENCE events. Each event belongs to an instruction, identified by its processor and its index in that processor's instruction stream, and an intra-instruction causality relation is given on the events; the *program order* $\mathrm{po}$ relates $e_1$ to $e_2$ if the instructions of $e_1$ and $e_2$ belong to the same processor and that of $e_1$ has the smaller index, or if $e_1$ precedes $e_2$ in intra-instruction causality. The events of each LOCK'd instruction form a group. An *execution witness* consists of a *memory order* $\mathrm{mo}$ and a *reads-from map* $\mathrm{rf}$, two relations on events, and an initial state, a partial map from locations to values. The witness is *valid* if $\mathrm{mo}$ is a partial order on the memory accesses, relating no other events, that is a linear order on the memory writes, if every pair $(w, r) \in \mathrm{rf}$ relates a read $r$ to a write $w$ of the same location and value, and if the following hold.

- For $(w, r) \in \mathrm{rf}$, if $w$ is a memory write, it is $\mathrm{mo}$-maximal among the writes to the location of $r$ that precede $r$ in $\mathrm{mo}$ or in $\mathrm{po}$, and if $w$ is a register write, it is $\mathrm{po}$-maximal among the writes to the location of $r$ that precede $r$ in $\mathrm{po}$. A read outside the range of $\mathrm{rf}$ takes the initial value of its location, and no write to that location precedes it in $\mathrm{mo}$ or in $\mathrm{po}$.
- $\mathrm{po}$ is included in $\mathrm{mo}$ for a memory read followed by any memory access, for a memory write followed by a memory write, for a memory write followed by a memory read with an MFENCE between them, and for any two memory accesses one of which belongs to a LOCK'd instruction.
- The memory accesses of each LOCK'd instruction are atomic in $\mathrm{mo}$: every other memory access precedes all of them or follows all of them.
- Every memory access has only finitely many $\mathrm{mo}$-predecessors, and for every memory write $w$ only finitely many accesses to the location of $w$ are unrelated to $w$ by $\mathrm{mo}$.

In particular, a memory write followed in program order by a read of the same location need not precede it in $\mathrm{mo}$; the first condition still makes the read see that write or a later one.

## Sources

- S. Owens, S. Sarkar and P. Sewell, "A better x86 memory model: x86-TSO", *TPHOLs 2009*, LNCS 5674, Springer, 2009, Section 3 (event structures) and Section 3.2 (execution witnesses and validity)
- P. Sewell, S. Sarkar, S. Owens, F. Zappa Nardelli and M. O. Myreen, "x86-TSO: a rigorous and usable programmer's model for x86 multiprocessors", *Communications of the ACM* 53(7):89–97, 2010
