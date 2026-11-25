# Correctness of mark-sweep collection

Let a heap $(H, \to, R)$ with roots be as in [correctness of the mark phase](correctness-of-the-mark-phase.md). A stop-the-world mark-sweep collection has two phases, with the mutator paused throughout:
- *marking:* the mark phase marks exactly the reachable cells $\mathrm{Reach}(R)$;
- *sweeping:* the sweep phase examines every cell of $H$, reclaims each unmarked cell onto the free list, and clears the mark of each marked cell.

**Theorem.** The collection reclaims exactly the unreachable cells $H \setminus \mathrm{Reach}(R)$. Afterwards no cell is marked, and the mutator-observable heap is unchanged: the reachable cells, the successor relation restricted to them, and the roots.

**Proof.** By the mark-phase theorem, the unmarked cells are exactly the unreachable ones, and sweeping reclaims exactly the unmarked cells. Reclaiming a cell changes only that cell. No reachable cell points to an unreachable one, because $\mathrm{Reach}(R)$ is closed under $\to$, so the pointers among reachable cells are untouched. Clearing marks restores the collector state for the next cycle.

## Depends on

- [Correctness of the mark phase](correctness-of-the-mark-phase.md)

## Sources

- P. R. Wilson, "Uniprocessor garbage collection techniques", in *Memory Management (IWMM 92)*, LNCS 637, Springer, 1992; extended version at <https://www.cs.cmu.edu/~fp/courses/15411-f14/misc/wilson94-gc.pdf>, Section 2.2: the two phases of mark-sweep collection, distinguishing live objects by tracing, then sweeping memory exhaustively to find the unmarked objects and reclaim them onto free lists. The proof above is written out here.
- R. Jones, A. Hosking and E. Moss, *The Garbage Collection Handbook*, CRC Press, 2011.
