# Reference counting does not reclaim cyclic garbage

Let a heap $(H, \to, R)$ with roots be as in [correctness of the mark phase](correctness-of-the-mark-phase.md). A *reference-counting* collector keeps for each cell the number of pointers to it from roots and from cells not yet reclaimed, updates the counts when pointers are created and destroyed, and reclaims a cell when its count drops to zero, decrementing the counts of its successors.

1. **Safety.** A reachable cell is never reclaimed: every reachable cell other than a root has a pointer from a reachable cell, and a root is referenced from the root set, so its count stays positive.
2. **Incompleteness.** A garbage cell that lies on a cycle of garbage cells is never reclaimed: each cell of the cycle keeps a positive count from its predecessor on the cycle, which is not reclaimed before it.

So a system that uses reference counting needs another collector, such as a tracing one, to reclaim cyclic garbage.

## Depends on

- [Correctness of the mark phase](correctness-of-the-mark-phase.md)

## Sources

- A. C. Myers, *Memory Management and Garbage Collection*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/gc/index.html>: section "Reference counting" (counts of incoming pointers, reclamation at count zero with decrements of the successors, and the remark that reference counting does not deal with cycles and must be combined with another method to reclaim them).
- P. R. Wilson, "Uniprocessor garbage collection techniques", in *Memory Management (IWMM 92)*, LNCS 637, Springer, 1992; extended version at <https://www.cs.cmu.edu/~fp/courses/15411-f14/misc/wilson94-gc.pdf>: Section 2.1 and Section 2.1.1 ("The Problem with Cycles": reference counting fails to reclaim cyclic garbage, so systems using it usually include another collector).
