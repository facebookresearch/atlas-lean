# Incremental cycle detection and strongly connected components in almost-linear total time

There is a deterministic algorithm that, given a directed graph undergoing $m$ edge insertions, reports the first insertion after which the graph contains a directed cycle, in total time $m\cdot\exp(O(\log^{167/168} m\log\log m))$. With the same total time bound one can explicitly maintain the strongly connected components of a directed graph undergoing $m$ edge insertions.

## Proof sketch

Give every edge capacity $1$ and cost $-1$, take $\mathbf{d} = \mathbf{0}$ and threshold $F = -1$: a circulation of negative cost exists exactly when the graph has a directed cycle, so *Incremental thresholded minimum-cost flow in almost-linear total time* detects the first such insertion. For components, run the IPM on a circulation instance and contract an edge once it carries a nontrivial amount of flow in the maintained circulation, which certifies that its endpoints are strongly connected; contraction preserves the circulation property, so the IPM continues on the contracted graph, and the number of contractions is at most $n - 1$.

## Depends on

- [Acyclic directed graph](../../../traversal-and-connectivity/topological-sorting/is-acyclic.md)
- [Strongly connected vertices](../../../traversal-and-connectivity/strongly-connected-components/strongly-connected.md)

## Proof depends on

- [Incremental thresholded minimum-cost flow in almost-linear total time](incremental-thresholded-mcf-almost-linear.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Simon Meierhans, Maximilian Probst Gutenberg, "Almost-Linear Time Algorithms for Incremental Graphs: Cycle Detection, SCCs, s-t Shortest Path, and Minimum-Cost Flow", STOC (2024), arXiv:2311.18295.
