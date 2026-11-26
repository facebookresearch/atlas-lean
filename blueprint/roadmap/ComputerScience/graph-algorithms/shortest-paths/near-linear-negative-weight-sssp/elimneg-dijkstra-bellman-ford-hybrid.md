# ElimNeg: the Dijkstra-Bellman-Ford hybrid runs in time proportional to the negative-edge counts of shortest paths

Let $G=(V,E,w)$ be a directed graph with integer weights, let $s\in V$ reach every vertex, and assume every vertex $v\ne s$ has out-degree $O(1)$. There is a deterministic algorithm $\mathrm{ElimNeg}(G,s)$ that, if $G$ has no negative cycle, computes $\mathrm{dist}_G(s,\cdot)$, hence a feasible price function for $G$, in time

$$
O\Big(\log n\cdot\Big(n+\sum_{v\in V}\eta_G(v;s)\Big)\Big).
$$

If $G$ has a negative cycle reachable from $s$, then $\sum_v\eta_G(v;s)=\infty$ and the algorithm does not terminate.

## Proof sketch

Maintain distance estimates $d(\cdot)$ and alternate a Dijkstra phase, which relaxes nonnegative edges from a binary-heap priority queue, with a Bellman-Ford phase, which relaxes every negative edge out of vertices updated in the previous phase. By induction on the number of negative edges, after $\eta_G(v;s)+1$ rounds $d(v)=\mathrm{dist}_G(s,v)$ along a shortest path attaining $\eta_G(v;s)$. A vertex enters the queue $O(1)$ times per round in which it is still improving, and constant out-degree bounds the relaxations per extraction, so the total number of heap operations is $O(\sum_v(\eta_G(v;s)+1))$, each costing $O(\log n)$.

## Depends on

- [The negative-edge count eta of shortest paths and the B-shifted graph](negative-edge-count-eta.md)
- [Price functions, reduced edge weights, and valid reweightings of a directed graph](price-functions-and-reduced-weights.md)

## Proof depends on

- [Dijkstra's algorithm with a binary heap](../../graph-algorithm-bounds/dijkstra-s-algorithm-with-a-binary-heap.md)
- [A feasible price function exists exactly when the graph has no negative cycle](feasible-potential-iff-no-negative-cycle.md)
- [Dense Dijkstra's algorithm](../dijkstra-s-algorithm/dijkstra.md)
- [Bellman–Ford algorithm](../bellman-ford-algorithm/bellman-ford.md)

## Sources

- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
- Yefim Dinitz, Rotem Itzhak, "Hybrid Bellman-Ford-Dijkstra algorithm", Journal of Discrete Algorithms 42 (2017).
