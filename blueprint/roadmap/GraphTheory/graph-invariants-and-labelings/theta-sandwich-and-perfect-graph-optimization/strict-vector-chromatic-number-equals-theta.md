# The strict vector chromatic number equals theta of the complement

For every finite simple graph $G$ with at least one edge,

$$
\chi_{sv}(G) = \vartheta(\overline{G}) ,
$$

where $\vartheta$ is the Lovasz theta function. Combined with the sandwich theorem for $\overline{G}$ this recovers $\omega(G) \le \chi_v(G) \le \vartheta(\overline{G}) \le \chi(G)$, so the vector chromatic number is a polynomial-time computable lower bound on $\chi(G)$ that is never weaker than the clique number.

## Proof sketch

The strict vector coloring program minimizes $\alpha$ subject to a positive semidefinite Gram matrix with unit diagonal and entries equal to $\alpha$ on edges; its semidefinite dual maximizes $-\sum_i p_{ii}$ over positive semidefinite $P$ with $\sum_{i \ne j} p_{ij} \ge 1$ and $p_{ij} = 0$ for non-adjacent distinct $i, j$. Both programs are strictly feasible, so their values agree, and the primal value is $-1/(\chi_{sv}(G) - 1)$. Writing an optimal $P$ as a Gram matrix of vectors $v_i$, the vanishing pattern says the $v_i$ form an orthogonal labeling of $\overline{G}$, and rescaling it into the min-max form of $\vartheta(\overline{G})$ identifies the dual value with $-1/(\vartheta(\overline{G}) - 1)$.

## Depends on

- [Vector colorings and the vector chromatic number](vector-colorings-and-vector-chromatic-number.md)
- [Lovász theta function](../theta-function-of-a-graph/lovasz-theta.md)

## Proof depends on

- [Orthogonal labeling of a graph](../theta-function-of-a-graph/is-orthogonal-labeling.md)
- [Vector chromatic numbers lie between the clique number and the chromatic number](vector-chromatic-number-bounds.md)
- [Lovász's sandwich theorem](../theta-function-of-a-graph/sandwich.md)

## Sources

- D. Karger, R. Motwani, M. Sudan, "Approximate Graph Coloring by Semidefinite Programming", Journal of the ACM 45 (1998), arXiv:cs/9812008.
- L. Lovasz, "On the Shannon capacity of a graph", IEEE Transactions on Information Theory 25 (1979).
- D. E. Knuth, "The Sandwich Theorem", Electronic Journal of Combinatorics 1 (1994), arXiv:math/9312214.
