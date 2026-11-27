# A negative sandwich with low-betweenness endpoints becomes r-remote after one valid reweighting

Let $G=(V,E^{+}\cup E^{-},w)$ with $w\ge 0$ on $E^{+}$, let $(x,U,y)$ be a negative sandwich and $\beta>1$ an integer. Define

$$
\phi(v)=\min\big(0,\max(d^\beta(x,v),-d^\beta(v,y))\big).
$$

Then (1) $\phi$ is valid; (2) every $v$ with $\mathrm{thru}^\beta(x,v,y)\ge 0$ lies outside the negative $(\beta-1)$-hop reach of $U$ in $G_\phi$. Consequently, if $b=\mathrm{BW}^\beta(x,y)$, then $U$ is $\min(\beta-1,n/b)$-remote in $G_\phi$, and $\phi$ is computable deterministically in $O(\beta m\log n)$ time. In particular, if $\mathrm{BW}^{r+1}(x,y)\le n/r$, then $U$ becomes $r$-remote in $O(rm\log n)$ time.

## Proof sketch

Validity is a case analysis with the triangle inequality: each of $0$, $d^\beta(x,\cdot)$ and $-d^\beta(\cdot,y)$ satisfies the edge inequality on nonnegative edges, and this is preserved under pointwise max and min. For $u\in U$ the sandwich gives $d^\beta(u,y)<0$, which forces $\phi(u)=0$; for $v$ not $\beta$-between $x$ and $y$ the max equals $d^\beta(x,v)$, so $\phi(v)\le d^\beta(x,v)$. Then $d^{\beta-1}_\phi(u,v)=d^{\beta-1}(u,v)-\phi(v)\ge d^1(x,u)+d^{\beta-1}(u,v)-d^\beta(x,v)\ge 0$ up to the strict inequality $d^1(x,u)<0$, so only $\beta$-between vertices can stay negatively reachable; the time bound is one $\beta$-hop computation from $x$ and one to $y$.

## Depends on

- [beta-betweenness of vertex pairs and negative sandwiches of negative vertices](beta-betweenness-and-negative-sandwiches.md)
- [r-remote sets and 1-hop independent sets of negative vertices](remote-and-independent-negative-sets.md)
- [Price functions, reduced edge weights, and valid reweightings of a directed graph](../near-linear-negative-weight-sssp/price-functions-and-reduced-weights.md)
- [Negative vertices, h-hop distances and the negative h-hop reach](negative-vertices-and-hop-distances.md)

## Proof depends on

- [Computing h-hop distances by alternating Dijkstra and Bellman-Ford rounds in O((h + 1)(m + n log n)) time](hop-limited-distances-hybrid.md)
- [Reweighting by a price function shifts every distance by the endpoint prices and preserves cycle weights](../near-linear-negative-weight-sssp/price-function-distance-shift.md)

## Sources

- Jeremy T. Fineman, "Single-Source Shortest Paths with Negative Real Weights in Õ(mn^(8/9)) Time", STOC (2024), arXiv:2311.02520.
