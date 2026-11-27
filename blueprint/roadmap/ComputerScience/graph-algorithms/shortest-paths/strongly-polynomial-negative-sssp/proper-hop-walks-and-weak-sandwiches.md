# Proper h-hop walks yield weak h-hop negative sandwiches of size Omega(sqrt(hk))

In split form, a *proper $h$-hop walk* is a walk with exactly $h$ negative edges whose negative vertices are pairwise distinct; $\hat d^h(s,t)$ denotes the infimum length of proper $h$-hop walks from $s$ to $t$. A *weak $h$-hop negative sandwich* is a triple $(s,U,t)$ with $d^h(s,u)+d^h(u,t)\le 0$ for all $u\in U$. Let $k=|N|$. Then:

1. for every integer $h\ge 1$ and $S\subseteq N$ there is an $O(h(m+n\log n))$-time algorithm returning a negative cycle, a pair $s,t\in S$ with $\hat d^h(s,t)<0$, or the distances $d(V,t)$ in the subgraph keeping only the negative edges of $S$;
2. for $h=\Omega(\log n)$ with $h\le k$ there is a randomized $O(h(m+n\log n))$-time algorithm returning a negative cycle, a weak $h$-hop sandwich $(s,U,t)$, or a set $S\subseteq N$ with all distances $d(V,\cdot)$ in the corresponding subgraph, such that with high probability $|U|,|S|=\Omega(\sqrt{hk})$;
3. for integers $r\ge 1$ and $h\ge 0$, if $(s,U,t)$ is a weak $h$-hop sandwich and $\mathrm{BW}^{r+h}(s,t)\le n/r$, then a valid price function making $U$ $r$-remote is computable in $O((r+h)(m+n\log n))$ time.

## Proof sketch

For item 1 compute $d^{h-1}(S,\cdot)$ and $d^h(S,\cdot)$; if they agree on $S$ the distances are final, and otherwise the walk attaining $d^h(S,t)<d^{h-1}(S,t)$ has exactly $h$ hops and either repeats a negative vertex, exposing a negative cycle, or is a proper negative $h$-hop walk. For item 2 sample each negative vertex with probability $1/q$, $q=2\sqrt{k/h}$; a sampled pair with $\hat d^h(s,t)<0$ forces at least $h-1$ sampled vertices of $B_{s,t}=\{u:d^h(s,u)+d^h(u,t)<0\}$, which by a multiplicative Chernoff bound is unlikely unless $|B_{s,t}|>\sqrt{kh}$, and $(s,B_{s,t},t)$ is returned. The restriction $h\le k$ is needed since $U,S\subseteq N$ have at most $k$ elements, while $\sqrt{hk}>k$ for $h>k$. Item 3 is the sandwich-to-remote argument with $\phi(v)=\max\{d^{r+h}(s,v),-d^{r+h}(v,t)\}$ on the vertices reachable from $s$, where it is finite, extended to the other vertices by the largest of these finite values.

## Depends on

- [beta-betweenness of vertex pairs and negative sandwiches of negative vertices](beta-betweenness-and-negative-sandwiches.md)
- [r-remote sets and 1-hop independent sets of negative vertices](remote-and-independent-negative-sets.md)
- [Negative vertices, h-hop distances and the negative h-hop reach](negative-vertices-and-hop-distances.md)
- [Price functions, reduced edge weights, and valid reweightings of a directed graph](../near-linear-negative-weight-sssp/price-functions-and-reduced-weights.md)

## Proof depends on

- [A negative sandwich with low-betweenness endpoints becomes r-remote after one valid reweighting](negative-sandwich-becomes-remote.md)
- [Computing h-hop distances by alternating Dijkstra and Bellman-Ford rounds in O(h(m + n log n)) time](hop-limited-distances-hybrid.md)

## Sources

- Yufan Huang, Peter Jin, Kent Quanrud, "Faster single-source shortest paths with negative real weights via proper hop distance", SODA (2025), arXiv:2407.04872.
