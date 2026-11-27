# Correctness of copying collection

Let a heap $(H, \to, R)$ with roots be as in [correctness of the mark phase](correctness-of-the-mark-phase.md), held in one half of memory, the *from-space*. A copying collection with Cheney's breadth-first algorithm copies the cells reachable from the roots into the other half, the *to-space*:
- it copies the root cells to the start of to-space, leaving in each copied cell of from-space a *forwarding pointer* to its copy;
- a *scan* pointer advances through to-space; at each cell it replaces every pointer into from-space by a pointer to the copy of its target, copying the target to the end of the copied cells (the *next* pointer) and leaving a forwarding pointer if the target has not been copied yet;
- it stops when the scan pointer reaches the next pointer, and the roles of the two halves are exchanged.

**Theorem.** The collection terminates, and the cells copied are exactly the reachable cells $\mathrm{Reach}(R)$. The copying map is a bijection from $\mathrm{Reach}(R)$ onto the copied cells that commutes with the successor relation and maps the roots to the new roots, so the mutator-observable heap is unchanged up to the renaming of cells. The work is proportional to the number of reachable cells and their pointers, not to the size of from-space, and the copies occupy a contiguous region of to-space.

**Proof sketch.** Cells before the scan pointer are *black*, with all pointers into to-space; cells between scan and next are *gray*, copied but not yet scanned. Each reachable cell is copied exactly once, because a forwarding pointer records its copy; only cells reached by following pointers from copied cells are copied, so only reachable cells are copied; and when scan meets next, the set of copied cells contains the roots and is closed under successors, as in the [mark phase](correctness-of-the-mark-phase.md).

## Depends on

- [Correctness of the mark phase](correctness-of-the-mark-phase.md)

## Sources

- A. C. Myers, *Memory Management and Garbage Collection*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/gc/index.html>: section "Copying collection" (from-space and to-space, forwarding pointers, Cheney's breadth-first algorithm with the scan and next pointers, black and gray copied objects, uncopied objects as garbage, and work proportional to the number of live objects).
- P. R. Wilson, "Uniprocessor garbage collection techniques", in *Memory Management (IWMM 92)*, LNCS 637, Springer, 1992; extended version at <https://www.cs.cmu.edu/~fp/courses/15411-f14/misc/wilson94-gc.pdf>: Section 2.4 (copying garbage collection, the Cheney algorithm with the scan pointer and the queue of copied objects).
