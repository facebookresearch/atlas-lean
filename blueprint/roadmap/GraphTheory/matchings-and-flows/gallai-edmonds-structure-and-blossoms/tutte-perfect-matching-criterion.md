# Tutte's perfect matching criterion via odd components of vertex deletions

A finite simple graph $G = (V, E)$ has a perfect matching if and only if

$$
o(G - X) \le |X| \qquad \text{for every } X \subseteq V .
$$

In particular every graph with a perfect matching has an even number of vertices (take $X = \emptyset$), and a graph has a near-perfect matching if and only if $\operatorname{def}(G) = 1$.

## Proof sketch

A perfect matching misses no vertex, so the odd-component bound gives $\operatorname{def}_G(X) \le 0$ for all $X$. Conversely, if $o(G - X) \le |X|$ for every $X$ then $\operatorname{def}(G) = 0$ and the Tutte-Berge formula gives $\nu(G) = |V|/2$. The statement about near-perfect matchings is the case $\operatorname{def}(G) = 1$ of the same formula.

## Depends on

- [Odd components and the Tutte deficiency of a vertex set](odd-components-and-tutte-deficiency.md)
- [Factor-critical graphs and near-perfect matchings](factor-critical-graphs.md)

## Proof depends on

- [Tutte-Berge min-max formula for the maximum matching size](tutte-berge-min-max-formula.md)
- [Every vertex set bounds the matching number through its odd components](odd-components-bound-matching-number.md)

## Sources

- W. T. Tutte, "The factorization of linear graphs", Journal of the London Mathematical Society 22 (1947).
- D. B. West, "A short proof of the Berge-Tutte Formula and the Gallai-Edmonds Structure Theorem", European Journal of Combinatorics 32 (2011).
