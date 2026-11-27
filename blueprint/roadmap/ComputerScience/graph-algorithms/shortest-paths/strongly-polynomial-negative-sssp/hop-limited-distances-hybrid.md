# Computing h-hop distances by alternating Dijkstra and Bellman-Ford rounds in O(h(m + n log n)) time

Let $G$ be in split form with all non-hop edges of nonnegative length. For every source set $S\subseteq V$ and $h\in\mathbb{N}$, the distances $d^h(S,v)$ for all $v\in V$ (with $d^h(S,v)=\infty$ when $v$ is not reachable from $S$), together with a walk attaining $d^h(S,v)$ for every $v$ at which it is finite, can be computed deterministically in $O((h+1)(m+n\log n))$ time, by $h+1$ Dijkstra passes interleaved with $h$ Bellman-Ford rounds, so with one Dijkstra pass even at $h=0$. Moreover:

1. if $d^{h+1}(s,v)=d^h(s,v)$ for every $v\in N$, then $d(s,v)=d^{h+1}(s,v)$ for every $v$, and if $G$ has no negative cycle this happens for some $h\le k$;
2. for every nonempty $S\subseteq V$ and $r\in\mathbb{N}$, the price functions $\phi_1(v)=d^r(S,v)$ and $\phi_2(v)=-d^r(v,S)$ are valid (they create no new negative edge) once made finite: $\phi_1$ takes the largest of its finite values at the vertices not reachable from $S$, and $\phi_2$ takes the smallest of its finite values at the vertices that cannot reach $S$.

## Proof sketch

The recurrence for $d^{h+1}$ is evaluated by one Dijkstra computation on an auxiliary graph seeded with the values $d^h(s,u)+\ell(u,u')$ at heads $u'$ of negative edges, so each additional hop costs $O(m+n\log n)$. Item 1 follows because any walk with more hops can be shortened through the recurrence without changing the minimum, and a shortest simple path has at most $k$ hops. For item 2, every non-negative edge $(u,v)$ satisfies $d^r(S,v)\le d^r(S,u)+\ell(u,v)$ since appending a non-hop edge does not increase the hop count, which is the validity condition; the second potential is symmetric. An edge leaving a vertex not reachable from $S$ ends at a vertex whose $\phi_1$ is finite or equal to the same largest value, so the finite extension keeps validity, and symmetrically for $\phi_2$.

## Depends on

- [Negative vertices, h-hop distances and the negative h-hop reach](negative-vertices-and-hop-distances.md)
- [Price functions, reduced edge weights, and valid reweightings of a directed graph](../near-linear-negative-weight-sssp/price-functions-and-reduced-weights.md)

## Proof depends on

- [Dijkstra's algorithm with a Fibonacci heap in O(m + n log n) word-RAM time](../dijkstra-priority-queue-costs/dijkstra-fibonacci-heap-word-ram.md)

## Sources

- Yefim Dinitz, Rotem Itzhak, "Hybrid Bellman-Ford-Dijkstra algorithm", Journal of Discrete Algorithms 42 (2017).
- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
- Jeremy T. Fineman, "Single-Source Shortest Paths with Negative Real Weights in Õ(mn^(8/9)) Time", STOC (2024), arXiv:2311.02520.
- Yufan Huang, Peter Jin, Kent Quanrud, "Faster single-source shortest paths with negative real weights via proper hop distance", SODA (2025), arXiv:2407.04872.
