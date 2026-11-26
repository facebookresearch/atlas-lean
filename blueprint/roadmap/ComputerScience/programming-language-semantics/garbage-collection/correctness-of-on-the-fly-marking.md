# Correctness of on-the-fly marking

Use the setting and the colors of [tri-color marking](tri-color-marking-and-its-invariants.md), in which the mutator and the collector run concurrently and every access to shared data is part of an atomic operation. Let the mutator repeat the atomic operation

> redirect an outgoing edge of a reachable node towards an already reachable node, and shade the new target,

and let the collector repeat:
- *marking*: shade all roots; then repeatedly visit the nodes, and on finding a gray node atomically make it black and shade its successors, until a complete pass over all nodes finds no gray node;
- *appending*: visit every node, appending each white node to the free list and making each black node white.

**Theorem.** The correctness criteria CC1 and CC2 hold. During each marking phase P1 is invariant, so at its end, when no gray node remains, every reachable node is black and every white node is garbage.

The mutator must shade the target of the new edge, not the old one, and the shading and the redirection cannot simply be separated into two atomic steps in the order shade, then redirect: that finer-grained variant is incorrect. A finer-grained variant that redirects first and shades afterwards is correct, with P2 and P3 in place of P1 as invariants.

## Depends on

- [Tri-color marking and its invariants](tri-color-marking-and-its-invariants.md)

## Proof depends on

- [Correctness of the mark phase](correctness-of-the-mark-phase.md)

## Sources

- E. W. Dijkstra, L. Lamport, A. J. Martin, C. S. Scholten and E. F. M. Steffens, "On-the-fly garbage collection: an exercise in cooperation", *Communications of the ACM* 21(11):966–975, 1978, <https://lamport.azurewebsites.net/pubs/garbage.pdf>: Section 4 (the coarse-grained mutator operation M1 and the coarse-grained collector, with Note 1 on shading the new rather than the old target, and the demonstration that CC1 and CC2 are met) and Section 5 (the incorrect finer-grained mutator that shades the future target first, found by Stenning and Woodger, and the solution with the invariants P2 and P3).

## Expansion

This page needs a source check before it is ready: the correctness argument for the finer-grained solution of Section 5, and the exact atomic steps of its mutator and collector, have still to be checked against the paper, since only the first coarse-grained solution and its proof were checked in full.
