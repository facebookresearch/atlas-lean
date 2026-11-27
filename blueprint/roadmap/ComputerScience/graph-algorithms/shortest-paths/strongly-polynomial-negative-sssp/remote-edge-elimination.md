# Eliminating r-remote negative edges by hop reduction in O~((k/r)m + rm) time

Let $G=(V,E^{+}\cup N,w)$ have $w(e)\ge 0$ on $E^{+}$, maximum degree $O(m/n)$, $\hat k=|N|$ negative edges, and suppose $N$ is $r$-remote. There is a deterministic algorithm running in $\tilde O((\hat k/r)m+rm)$ time that either correctly reports that $G$ contains a negative cycle or computes a valid price function that neutralizes every edge of $N$.

## Proof sketch

Vertices outside the negative $r$-hop reach have $\delta_i(u)=0$ for all $i\le r$, so all their layered copies receive identical incident weights and can be contracted into the single copy $u_0$. The layered $r$-hop reduction then consists of $r$ copies of the remote subgraph, which has at most $n/r$ vertices and hence $O(m/r)$ edges by the degree bound, plus one copy of $G$, for $O(m)$ edges in total. Computing $\delta_0,\dots,\delta_r$ costs $\tilde O(rm)$, and the Johnson potentials $\mathrm{dist}_G(V,\cdot)$ follow from $\lceil\hat k/r\rceil$-hop distances in $H$ in $\tilde O((\hat k/r)m)$ time, a persisting improvement signalling a negative cycle.

## Depends on

- [r-remote sets and 1-hop independent sets of negative vertices](remote-and-independent-negative-sets.md)
- [Price functions, reduced edge weights, and valid reweightings of a directed graph](../near-linear-negative-weight-sssp/price-functions-and-reduced-weights.md)

## Proof depends on

- [Computing h-hop distances by alternating Dijkstra and Bellman-Ford rounds in O((h + 1)(m + n log n)) time](hop-limited-distances-hybrid.md)
- [r-hop reductions and the layered hop-reducing auxiliary graph](r-hop-reduction-auxiliary-graph.md)

## Sources

- Jeremy T. Fineman, "Single-Source Shortest Paths with Negative Real Weights in Õ(mn^(8/9)) Time", STOC (2024), arXiv:2311.02520.
