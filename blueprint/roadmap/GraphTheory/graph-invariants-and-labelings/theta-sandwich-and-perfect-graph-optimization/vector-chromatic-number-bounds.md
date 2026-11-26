# Vector chromatic numbers lie between the clique number and the chromatic number

For every finite simple graph $G$ with at least one edge,

$$
\omega(G) \le \chi_v(G) \le \chi_{sv}(G) \le \chi(G) .
$$

## Proof sketch

The middle inequality is immediate since a strict vector coloring is a vector coloring. Given a proper coloring with $k$ colors, send each color class to one vertex of a regular simplex with $k$ vertices centred at the origin and scaled to unit length; distinct simplex vertices have inner product exactly $-1/(k - 1)$, giving a strict vector $k$-coloring. For a clique $Q$ of size $q$ in a vector $k$-coloring, $0 \le \|\sum_{v \in Q} u_v\|^2 \le q - q(q - 1)/(k - 1)$, which forces $k \ge q$.

## Depends on

- [Vector colorings and the vector chromatic number](vector-colorings-and-vector-chromatic-number.md)

## Sources

- D. Karger, R. Motwani, M. Sudan, "Approximate Graph Coloring by Semidefinite Programming", Journal of the ACM 45 (1998), arXiv:cs/9812008.
