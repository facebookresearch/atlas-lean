# Minimum spanning trees contain bottleneck paths

Let $G$ be a connected graph with $n$ vertices, $m$ edges and real edge weights $\omega$, not necessarily distinct. The *bottleneck* of a path is the largest weight of an edge on it, and a *bottleneck path* between distinct vertices $s$ and $t$ is a path from $s$ to $t$ whose bottleneck is minimal. If $T$ is a minimum spanning tree of $G$, a spanning tree of least total weight, the unique path from $s$ to $t$ in $T$ is a bottleneck path: if its heaviest edge $e$ were heavier than the bottleneck of some path from $s$ to $t$, that path would have an edge $f$ joining the two components of $T - e$ with $\omega(f) < \omega(e)$, and $T - e + f$ would be a lighter spanning tree. A bottleneck path can be computed in $O(n + m)$ time. Break ties among the weights by edge index; a path that is bottleneck for this total order is bottleneck for $\omega$. Then find the lower median $w$ of the edge weights in this order by linear-time selection, stopping when one edge remains. If $s$ and $t$ are joined by edges of weight at most $w$, delete the heavier edges and keep only the component of $s$; otherwise contract the components of the edges of weight at most $w$. Each round on $m \ge 2$ edges leaves at most $\lceil m/2 \rceil \le 2m/3$ of them and keeps $n \le m + 1$, so the costs form a geometric series. Alternatively, Kruskal's algorithm followed by a tree traversal takes $O(m \log n)$ time; Kruskal's algorithm uses only the order of the weights, so its correctness for natural-number weights applies after replacing each weight by its rank.

## Related topics

- [Minimum spanning tree of a vertex list](../../approximation-algorithms/double-tree-approximation-for-metric-tsp/is-min-spanning.md)

## Proof depends on

- [Kruskal's output is a spanning forest](../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/kruskal-is-spanning-forest.md)
- [Kruskal's algorithm gives a minimum spanning forest](../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/kruskal-minimal.md)
- [Median of medians makes linearly many comparisons](../../sorting-and-searching/median-of-medians/median-of-medians-time.md)
- [Correctness of median-of-medians selection](../../sorting-and-searching/median-of-medians/median-of-medians-correct.md)


## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Fréchet distance: How to walk your dog" (Chapter 33), <https://sarielhp.org/book/chapters/frechet.pdf>: Definition 33.1.4 (bottleneck edge and bottleneck path) and Claim 33.1.5 with its proof by exchanging edges outside the minimum spanning tree
