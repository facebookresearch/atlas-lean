# Minimum spanning trees contain bottleneck paths

Let $G$ be a connected graph with $n$ vertices, $m$ edges and real edge weights $\omega$, not necessarily distinct. The *bottleneck* of a path is the largest weight of an edge on it, and a *bottleneck path* between vertices $s$ and $t$ is a path from $s$ to $t$ whose bottleneck is minimal. If $T$ is a minimum spanning tree of $G$, a spanning tree of least total weight, the unique path from $s$ to $t$ in $T$ is a bottleneck path: if its heaviest edge $e$ were heavier than the bottleneck of some path from $s$ to $t$, that path would have an edge $f$ joining the two components of $T - e$ with $\omega(f) < \omega(e)$, and $T - e + f$ would be a lighter spanning tree. Consequently a bottleneck path can be computed in $O(m \log n)$ time, by Kruskal's algorithm followed by a tree traversal; Kruskal's algorithm uses only the order of the weights, so its correctness for natural-number weights applies after replacing each weight by its rank.

## Proof depends on

- [Kruskal's output is a spanning forest](../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/kruskal-is-spanning-forest.md)
- [Kruskal's algorithm gives a minimum spanning forest](../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/kruskal-minimal.md)

## Informally uses

- [Minimum spanning tree of a vertex list](../../approximation-algorithms/double-tree-approximation-for-metric-tsp/is-min-spanning.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Fréchet distance: How to walk your dog" (Chapter 33), <https://sarielhp.org/book/chapters/frechet.pdf>: Definition 33.1.4 (bottleneck edge and bottleneck path) and Claim 33.1.5 with its proof by exchanging edges outside the minimum spanning tree
