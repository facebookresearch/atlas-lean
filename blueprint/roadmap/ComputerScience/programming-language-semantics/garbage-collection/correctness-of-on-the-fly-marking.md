# Correctness of on-the-fly marking

Use the setting and the colors of [tri-color marking](tri-color-marking-and-its-invariants.md), in which the mutator and the collector run concurrently, every access to shared data is part of an atomic operation, every node is white initially, and appending a node to the free list redirects its outgoing edges so that only NIL or free nodes can be reached from it. Let the mutator repeat the atomic operation

> M1: redirect an outgoing edge of a reachable node towards an already reachable node, and shade the new target,

and let the collector repeat:
- *marking*: shade all roots; then repeatedly visit the nodes, and on finding a gray node atomically make it black and shade its successors, until a complete pass over all nodes finds no gray node;
- *appending*: visit every node, appending each white node to the free list and making each black node white, so that no black node remains.

**Theorem.** For this coarse-grained algorithm the correctness criteria CC1 and CC2 hold. During each marking phase P1 is invariant, so at its end, when no gray node remains, every reachable node is black and every white node is garbage.

To maintain P1, the mutator must shade the target of the new edge, not the old one. Splitting M1 into two atomic steps in the order shade, then redirect, while keeping P1, is incorrect: the shading can be undone by an appending phase before the edge is placed. A second coarse-grained mutator, which atomically shades the target of the previously redirected edge and redirects an outgoing edge of a reachable node towards a reachable node, is correct with the same collector, with P2 and P3 in place of P1.

## Depends on

- [Tri-color marking and its invariants](tri-color-marking-and-its-invariants.md)

## Proof depends on

- [Correctness of the mark phase](correctness-of-the-mark-phase.md)

## Sources

- E. W. Dijkstra, L. Lamport, A. J. Martin, C. S. Scholten and E. F. M. Steffens, "On-the-fly garbage collection: an exercise in cooperation", *Communications of the ACM* 21(11):966–975, 1978, <https://lamport.azurewebsites.net/pubs/garbage.pdf>: Section 4 (marking from an all-white start, the coarse-grained mutator operation M1 and the coarse-grained collector, with Note 1 on shading the new rather than the old target, Note 2 on appending, the demonstration that CC1 and CC2 are met, and, at its end, the incorrect finer-grained mutator that shades the future target first, found by Stenning and Woodger) and Section 5 (the second coarse-grained mutator M2 and its proof with the invariants P2 and P3). The fine-grained solution of Section 6, which splits the operations of both mutator and collector, is not stated here.
