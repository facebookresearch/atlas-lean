# Polynomial-time stable sets, cliques and optimal colorings of perfect graphs

There are polynomial-time algorithms that, for every perfect graph $G$ and integer vertex weights $w \ge 0$, compute a maximum-weight stable set, a maximum-weight clique, an optimal coloring with $\chi(G)$ colors and a minimum clique cover. These algorithms use the ellipsoid method through the computability of $\vartheta$; for each fixed $\omega$, Chudnovsky, Lagoutte, Seymour and Spirkl color perfect graphs with clique number at most $\omega$ in time $O(n^{f(\omega)})$ by a combinatorial algorithm, while a combinatorial polynomial-time optimal coloring algorithm for all perfect graphs is not known.

## Proof sketch

For perfect $G$ the stable set polytope equals the theta body, so $\vartheta(G, w) = \alpha(G, w)$, an integer; computing $\vartheta(G, w)$ within $1/3$ therefore gives $\alpha(G, w)$ exactly, and deleting vertices one at a time whenever the value does not drop finds a maximum-weight stable set. Cliques are handled in $\overline{G}$, which is perfect by the weak perfect graph theorem. For coloring, one finds with polynomially many weighted stable-set computations a stable set meeting every maximum clique; removing it lowers $\omega$ by one, and repeating $\omega(G) = \chi(G)$ times colors $G$ optimally.

## Depends on

- [Perfect graph](../../graph-coloring/part-01/perfect-graphs/is-perfect.md)
- [Lovász theta function](../theta-function-of-a-graph/lovasz-theta.md)

## Proof depends on

- [Polynomial-time computability of the weighted Lovasz theta function](polynomial-time-computability-of-theta.md)
- [Theta equals the independence number on perfect graphs](../theta-function-of-a-graph/lovasz-theta-eq-indep-num-of-is-perfect.md)
- [Perfect graphs are those with STAB = QSTAB](../theta-function-of-a-graph/is-perfect-iff-stab-eq-qstab.md)
- [Weak perfect graph theorem](../../graph-coloring/part-01/perfect-graphs/lovasz-weak-perfect-graph-general.md)
- [Stable set polytope](../theta-function-of-a-graph/stab.md)
- [Theta body](../theta-function-of-a-graph/th.md)

## Sources

- M. Grotschel, L. Lovasz, A. Schrijver, "Polynomial algorithms for perfect graphs", Annals of Discrete Mathematics 21 (1984).
- M. Grotschel, L. Lovasz, A. Schrijver, "Geometric Algorithms and Combinatorial Optimization", Springer (1988).
- M. Chudnovsky, A. Lagoutte, P. Seymour, S. Spirkl, "Colouring perfect graphs with bounded clique number", Journal of Combinatorial Theory Series B 122 (2017).
