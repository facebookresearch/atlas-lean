# Largest Induced Path Size

The size of a largest induced path of $G$, as a natural number.

A subset $s \subseteq V(G)$ is an *induced path* when the induced subgraph
`G.induce s` is a tree in which every vertex has degree at most $2$
(equivalently: a tree that is itself a path graph). We define
`largestInducedPathSize G` as the supremum of `s.card` over all such subsets.

This is *not* the `SimpleGraph.path` invariant of Mathlib, which is the floor of
the average distance.
