# Correctness of the mark phase

Model a heap as a finite set $H$ of cells, a successor relation ${\to} \subseteq H \times H$ recording the pointers stored in each cell, and a set $R \subseteq H$ of *roots*, the cells referenced directly from global variables, the stack and registers. A cell is *reachable* if it lies on a directed path of pointers starting at a root, that is, if it belongs to the least set $\mathrm{Reach}(R)$ that contains $R$ and is closed under $\to$. Reachable cells are *live*. Unreachable cells are *garbage*: no sequence of program actions can access them.

**Theorem.** The mark phase starts with all cells unmarked and a worklist containing $R$, marking each root. It then repeatedly removes a cell $c$ from the worklist and, for each successor $c \to d$ with $d$ unmarked, marks $d$ and adds it to the worklist. This traversal is depth first if the worklist is a stack and breadth first if it is a queue. It terminates and marks exactly $\mathrm{Reach}(R)$.

**Proof.**
- *Termination.* Each cell is marked, and therefore added to the worklist, at most once, and $H$ is finite.
- *Only reachable cells are marked.* Roots are reachable, and a cell is marked only as a successor of a marked cell, so by induction every marked cell is reachable.
- *All reachable cells are marked.* Every cell added to the worklist is eventually removed and its successors examined. So when the worklist is empty, the set of marked cells contains $R$ and is closed under $\to$, and it therefore contains $\mathrm{Reach}(R)$.

## Sources

- P. R. Wilson, "Uniprocessor garbage collection techniques", in *Memory Management (IWMM 92)*, LNCS 637, Springer, 1992; extended version at <https://www.cs.cmu.edu/~fp/courses/15411-f14/misc/wilson94-gc.pdf>:
    - Section 1 (the liveness criterion: the root set, reachability along directed paths of pointers, and garbage as unreachable objects);
    - Section 2.2 (mark-sweep collection: tracing from the root set by a depth-first or breadth-first traversal, marking the objects reached); the invariant proof above is written out here.
- R. Jones, A. Hosking and E. Moss, *The Garbage Collection Handbook*, CRC Press, 2011.
