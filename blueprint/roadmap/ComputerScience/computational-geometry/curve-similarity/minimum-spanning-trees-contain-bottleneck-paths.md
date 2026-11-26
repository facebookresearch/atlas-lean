# Minimum spanning trees contain bottleneck paths

Let $G$ be a connected graph with $n$ vertices, $m$ edges and pairwise distinct edge weights $\omega$. The *bottleneck* of a path is the largest weight of an edge on it, and a *bottleneck path* between vertices $s$ and $t$ is a path from $s$ to $t$ whose bottleneck is minimal. If $T$ is the minimum spanning tree of $G$, the unique path from $s$ to $t$ in $T$ is a bottleneck path. Consequently a bottleneck path can be computed in $O(n + m)$ expected time, by a randomized linear-time minimum spanning tree algorithm followed by a tree traversal.

## Informally uses

- [Minimum spanning tree of a vertex list](../../approximation-algorithms/double-tree-approximation-for-metric-tsp/is-min-spanning.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Fréchet distance: How to walk your dog" (Chapter 33), <https://sarielhp.org/book/chapters/frechet.pdf>: Definition 33.1.4 (bottleneck edge and bottleneck path) and Claim 33.1.5 with its proof by exchanging edges outside the minimum spanning tree
