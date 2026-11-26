# Tri-color marking and its invariants

Let a heap be a directed graph of nodes with a set of roots, as in [correctness of the mark phase](correctness-of-the-mark-phase.md), whose free list is linked from special roots so that free nodes count as reachable. A *mutator* changes the graph only by redirecting an outgoing edge of a reachable node towards an already reachable node, and a *collector* repeats a *marking phase*, which should mark every reachable node, followed by an *appending phase*, which appends every unmarked node to the free list and removes the marks. Appending a node to the free list includes redirecting its outgoing edges so that only NIL or free nodes can be reached from it.

Marking uses three colors: every node is *white*, *gray* or *black*, gray being darker than white and lighter than black. Initially every node is white, and each appending phase whitens the black nodes, so every marking phase starts without black nodes. *Shading* a node makes it gray if it is white and leaves it unchanged otherwise. During a marking phase no node becomes lighter. The following relations are used as invariants:
- **P1** (*strong tricolor invariant*): no edge points from a black node to a white node.
- **P2**: for each white reachable node there is a *propagation path* leading to it, that is, a path starting at a gray node and consisting solely of edges with white targets.
- **P3**: only the last edge placed by the mutator may lead from a black node to a white node.

The cooperation of mutator and collector is correct if:
- **CC1**: every garbage node present at the beginning of an appending phase has been appended to the free list by the end of the next appending phase;
- **CC2**: appending a garbage node to the free list is the collector's only modification of the shape of the graph.

## Depends on

- [Correctness of the mark phase](correctness-of-the-mark-phase.md)

## Sources

- E. W. Dijkstra, L. Lamport, A. J. Martin, C. S. Scholten and E. F. M. Steffens, "On-the-fly garbage collection: an exercise in cooperation", *Communications of the ACM* 21(11):966–975, 1978, <https://lamport.azurewebsites.net/pubs/garbage.pdf>: Section 1 (the graph, roots, reachability and garbage), Section 3 (the free list made reachable, the single mutator operation, the two phases of the collector, and the correctness criteria CC1 and CC2), Section 4 (marking starts with all nodes white; Note 2: appending a node redirects its outgoing edges so that only NIL or free nodes are reachable from it) and Sections 4–5 (the colors white, gray and black, shading, the monotonicity argument, and the invariants P1, P2 with propagation paths, and P3).
- A. C. Myers, *Memory Management and Garbage Collection*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/gc/index.html>: section "Concurrent and incremental collection" (the tricolor invariant that black objects do not point to white objects, and read and write barriers that preserve it).
