# r-remote sets and 1-hop independent sets of negative vertices

Let $G=(V,E^{+}\cup E^{-},\ell)$ be in split form with $n=|V|$, $\ell(e)\ge 0$ on $E^{+}$, and let $X\subseteq N$ be a set of negative vertices. For $r\in\mathbb{N}$, $X$ is *$r$-remote* if its negative $r$-hop reach satisfies $|R^r(X)|\le n/r$; the outgoing (negative) edges of $X$ are then called *$r$-remote edges*, and the subgraph induced by $R^r(X)$ is an *$r$-remote subgraph*. A set $I\subseteq N$ is a *$1$-hop independent set* if $d^1(I,x)\ge 0$ for every $x\in I$, where hops are counted only along negative edges leaving $I$; equivalently, no negative edge of $I$ can be followed, within one hop, by a negative-length walk into another vertex of $I$.

## Depends on

- [Negative vertices, h-hop distances and the negative h-hop reach](negative-vertices-and-hop-distances.md)

## Sources

- Jeremy T. Fineman, "Single-Source Shortest Paths with Negative Real Weights in Õ(mn^(8/9)) Time", STOC (2024), arXiv:2311.02520.
- Yufan Huang, Peter Jin, Kent Quanrud, "Faster single-source shortest paths with negative real weights via proper hop distance", SODA (2025), arXiv:2407.04872.
