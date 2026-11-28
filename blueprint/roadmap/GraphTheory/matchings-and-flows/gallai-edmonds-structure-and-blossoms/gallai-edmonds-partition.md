# The Gallai-Edmonds partition D(G), A(G), C(G)

Let $G = (V, E)$ be a finite simple graph. Define

$$
D(G) = \{ v \in V : \text{some maximum matching of } G \text{ misses } v \},
$$

$A(G) = N(D(G)) \setminus D(G)$, the vertices outside $D(G)$ having a neighbour in $D(G)$, and $C(G) = V \setminus (D(G) \cup A(G))$. The triple $(D(G), A(G), C(G))$ is the *Gallai-Edmonds partition* of $V$. A vertex $v$ lies outside $D(G)$ exactly when $\nu(G - v) = \nu(G) - 1$, that is, when every maximum matching covers $v$.

## Depends on

- [Odd components and the Tutte deficiency of a vertex set](odd-components-and-tutte-deficiency.md)
- [Factor-critical graphs and near-perfect matchings](factor-critical-graphs.md)

## Sources

- T. Gallai, "Neuer Beweis eines Tutte'schen Satzes", Magyar Tud. Akad. Mat. Kutato Int. Kozl. 8 (1963).
- J. Edmonds, "Paths, trees, and flowers", Canadian Journal of Mathematics 17 (1965).
- L. Lovasz, M. D. Plummer, "Matching Theory", Annals of Discrete Mathematics 29, North-Holland (1986).
