# Negative vertices, h-hop distances and the negative h-hop reach

Let $G=(V,E,\ell)$ be real-weighted. For $v\in V$ let $\mu_v=\min\big(\{0\}\cup\{\ell(v,x):(v,x)\in E\}\big)$, so $\mu_v=0$ when $v$ has no outgoing edge of negative length, a sink included. The *split graph* $G'$ replaces each $v$ by $v^-,v^+$ joined by an arc $(v^-,v^+)$ of length $\mu_v$, and each arc $(u,v)$ by $(u^+,v^-)$ of length $\ell(u,v)-\mu_u\ge 0$. Then $G'$ has $O(n)$ vertices and $O(m)$ edges, distances in $G'$ determine those in $G$, and every negative edge of $G'$ is the unique outgoing edge of its tail and the unique incoming edge of its head. Assume henceforth this form; identify each negative edge with its tail, a *negative vertex*, let $N$ be the set of negative vertices and $k=|N|$.

For a walk, its *hops* are its negative edges counted with multiplicity. For $h\in\mathbb{N}$ and $s,t\in V$, $d^h(s,t)$ is the infimum length of walks from $s$ to $t$ with at most $h$ hops; for sets, $d^h(S,T)=\min_{s\in S,t\in T}d^h(s,t)$. Hop distances satisfy

$$
d^{h+1}(s,t)=\min\Big\{d^h(s,t),\ \min_{u\in N}\big(d^h(s,u)+d^1(u,t)\big)\Big\}.
$$

The *negative $h$-hop reach* of $X\subseteq N$ is $R^h(X)=\{v\in V: d^h(X,v)<0\}$. Within one round of reweighting, the set $N$ is frozen, so a reweighted negative edge remains a hop even if its length becomes nonnegative.

## Depends on

- [Real-weighted negative SSSP in the real RAM and strongly polynomial running time](real-weighted-sssp-strongly-polynomial.md)
- [Price functions, reduced edge weights, and valid reweightings of a directed graph](../near-linear-negative-weight-sssp/price-functions-and-reduced-weights.md)

## Sources

- Jeremy T. Fineman, "Single-Source Shortest Paths with Negative Real Weights in Õ(mn^(8/9)) Time", STOC (2024), arXiv:2311.02520.
- Yufan Huang, Peter Jin, Kent Quanrud, "Faster single-source shortest paths with negative real weights via proper hop distance", SODA (2025), arXiv:2407.04872.
