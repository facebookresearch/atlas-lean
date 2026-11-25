# Correctness of the Hungarian algorithm

For a bipartite graph $G = (V, E)$ with weights $w$, the Hungarian method builds extreme matchings $M_0, M_1, \dots$ (each of maximum weight among matchings of its size) by augmenting along a shortest $M$-augmenting path for the length $w$ on matching edges and $-w$ elsewhere; the auxiliary digraph has no negative cycle, and the heaviest $M_k$ is a maximum-weight matching. Computing each shortest path by the Bellman–Ford method gives $O(|V|^2|E|)$ time; keeping vertex potentials that make all lengths nonnegative allows Dijkstra's method instead and gives $O(|V|(|E| + |V|\log|V|))$ time, which is $O(n^3)$ for the $n \times n$ assignment problem (the source states this refinement without proof). Optimality is certified by Egerváry's theorem: the maximum weight of a matching equals the minimum of $\sum_v y_v$ over $y \ge 0$ with $y_u + y_v \ge w_e$ on every edge $uv$, and $y$ can be taken integral when $w$ is. A minimum-cost assignment is the case $G = K_{n,n}$ with weights $M - c_{ij}$ for a constant $M$ making all weights positive.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Optimality certificate for the assignment problem from feasible dual potentials with equality on the chosen permutation.
- Shortest paths for real arc lengths in a digraph without negative cycles: existence, and computation in $O(|V||E|)$ time.
- Dijkstra's method with vertex potentials (nonnegative reduced lengths) for the refined bound.

## Background

- [Kőnig's theorem for finite bipartite graphs](../../../GraphTheory/matchings-and-flows/k-nig-s-theorem/konig-matching-cover.md): the unweighted case of the min–max relation.
- [Linear functionals on doubly stochastic matrices are bounded below at a permutation](../../../LinearAlgebra/positive-definite-matrices/von-neumann-s-trace-inequality/exists-perm-sum-le-of-mem-doubly-stochas.md): the assignment LP attains its minimum at a permutation.
- [Bellman-Ford succeeds exactly when no negative cycle is reachable](../shortest-paths/bellman-ford-algorithm/bellman-ford-returns-distances-iff.md): Bellman–Ford for integer weights.
- [Correctness of Johnson's algorithm](../shortest-paths/johnson-s-algorithm/johnson-distance-spec.md): reweighting by vertex potentials for integer weights.

## Sources

- A. Schrijver, *A Course in Combinatorial Optimization*, lecture notes, CWI and University of Amsterdam, 2017, <https://homepages.cwi.nl/~lex/files/dict.pdf>, §3.5, Proposition 1, Theorems 3.5–3.6 and the remark after Theorem 3.6 (Dijkstra with potentials)
- A. Schrijver, *A Course in Combinatorial Optimization*, lecture notes, CWI and University of Amsterdam, 2017, <https://homepages.cwi.nl/~lex/files/dict.pdf>, §3.6, Corollary 3.7b and Theorem 3.8
