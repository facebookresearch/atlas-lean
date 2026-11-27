# A feasible price function exists exactly when the graph has no negative cycle

Let $G=(V,E,w)$ be a directed graph with real weights and let $G_s$ be obtained by adding a new vertex $s$ and an edge $(s,v)$ of weight $0$ for every $v\in V$. Then $G$ admits a feasible price function if and only if $G$ has no cycle of negative weight. If $G$ has no negative cycle, then

$$
\phi(v)=\mathrm{dist}_{G_s}(s,v)=\min_{u\in V}\mathrm{dist}_G(u,v)\le 0
$$

is a feasible price function. Given any feasible $\phi$, single-source distances from any $x\in V$ in $G$ are obtained from one run of Dijkstra's algorithm on $G_\phi$ followed by the correction $\mathrm{dist}_G(x,v)=\mathrm{dist}_{G_\phi}(x,v)-\phi(x)+\phi(v)$, in $O((m+n)\log n)$ total time with a binary heap.

## Proof sketch

If $G$ has no negative cycle, every vertex of $G_s$ has a finite distance from $s$, and the triangle inequality $\mathrm{dist}(s,v)\le\mathrm{dist}(s,u)+w(u,v)$ is exactly $w_\phi(u,v)\ge 0$. Conversely, if $\phi$ is feasible then every cycle $C$ satisfies $w(C)=w_\phi(C)\ge 0$ by the distance-shift lemma. The final claim follows from the same lemma, since Dijkstra's algorithm is correct on the nonnegative weights $w_\phi$.

## Depends on

- [Johnson's algorithm](../johnson-s-algorithm/johnson.md)
- [Price functions, reduced edge weights, and valid reweightings of a directed graph](price-functions-and-reduced-weights.md)

## Proof depends on

- [Reweighting by a price function shifts every distance by the endpoint prices and preserves cycle weights](price-function-distance-shift.md)
- [Dijkstra's algorithm with a binary heap](../../graph-algorithm-bounds/dijkstra-s-algorithm-with-a-binary-heap.md)

## Sources

- Donald B. Johnson, "Efficient Algorithms for Shortest Paths in Sparse Networks", Journal of the ACM 24(1) (1977).
- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
