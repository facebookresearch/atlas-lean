# Reweighting by a price function shifts every distance by the endpoint prices and preserves cycle weights

Let $G=(V,E,w)$ be a directed graph with real weights and let $\phi:V\to\mathbb{R}$ be a price function. For every directed walk $P$ from $u$ to $v$,

$$
w_\phi(P)=w(P)+\phi(u)-\phi(v).
$$

Consequently $w_\phi(C)=w(C)$ for every closed walk $C$; for all $u,v\in V$ one has $\mathrm{dist}_{G_\phi}(u,v)=\mathrm{dist}_G(u,v)+\phi(u)-\phi(v)$ (with $\pm\infty$ preserved); and $G$ and $G_\phi$ are equivalent. If a fixed edge set $F\subseteq E$ is designated as *hop edges* and $\mathrm{dist}^h(u,v)$ denotes the infimum weight of $u$-$v$ walks using at most $h$ edges of $F$ (counted with multiplicity), then also $\mathrm{dist}^h_{G_\phi}(u,v)=\mathrm{dist}^h_G(u,v)+\phi(u)-\phi(v)$ for every $h\ge 0$.

## Proof sketch

Write $P=(x_0=u,x_1,\dots,x_\ell=v)$. Summing $w_\phi(x_{i-1},x_i)=w(x_{i-1},x_i)+\phi(x_{i-1})-\phi(x_i)$ over $i$ telescopes the price terms to $\phi(u)-\phi(v)$. For a closed walk the price terms cancel. Since every $u$-$v$ walk is shifted by the same constant, minimizers (and the infimum, including $\pm\infty$) are preserved, and the same holds after restricting to walks with at most $h$ hop edges because reweighting does not change which edges are designated as hops.

## Depends on

- [Price functions, reduced edge weights, and valid reweightings of a directed graph](price-functions-and-reduced-weights.md)

## Sources

- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
- Donald B. Johnson, "Efficient Algorithms for Shortest Paths in Sparse Networks", Journal of the ACM 24(1) (1977).
- Jeremy T. Fineman, "Single-Source Shortest Paths with Negative Real Weights in Õ(mn^(8/9)) Time", STOC (2024), arXiv:2311.02520.
