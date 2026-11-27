# The union of pseudodisks has linear complexity

1. The union of a collection of convex polygonal pseudodisks with $n$ vertices in total has complexity $O(n)$: its boundary has $O(n)$ vertices and edges.
2. More precisely, let $\Gamma$ be a set of $n \ge 3$ closed Jordan curves in the plane in general position (no three through a common point), any two of which are disjoint or cross in exactly two points, and consider the regions they bound. The boundary of the union of these regions consists of at most $6n - 12$ arcs, each a connected piece of one curve of $\Gamma$ (Kedem, Livne, Pach and Sharir).

## Depends on

- [Minkowski sums of convex polygons with disjoint interiors are pseudodisks](minkowski-sums-of-disjoint-convex-sets-are-pseudodisks.md)

## Proof depends on

- [Edge and face bounds for planar graphs](../../../GraphTheory/planar-graphs-and-minors/edge-and-face-bounds-for-planar-graphs.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 34, Lemma 2 (the union of polygonal pseudodisks with $n$ vertices in total has complexity $O(n)$) and its charging proof

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Union complexity of pseudodisks" (Chapter 18), <https://sarielhp.org/book/chapters/union_pseudodisks.pdf>: Section 18.1 (pseudodisks as closed Jordan curves meeting pairwise in two points or not at all, and the union complexity $\langle \Gamma \rangle$) and Theorem 18.2.6 (at most $6n - 12$)
