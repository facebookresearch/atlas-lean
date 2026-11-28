# Tutte-Berge min-max formula for the maximum matching size

For every finite simple graph $G = (V, E)$,

$$
\nu(G) = \min_{X \subseteq V} \frac{|V| + |X| - o(G - X)}{2} = \frac{|V| - \operatorname{def}(G)}{2} .
$$

Equivalently, a maximum matching of $G$ misses exactly $\operatorname{def}(G)$ vertices. In particular, $G$ has a near-perfect matching, one missing exactly one vertex, if and only if $\operatorname{def}(G) = 1$.

## Proof sketch

The inequality $\le$ is the odd-component bound. For $\ge$ (Anderson's method as presented by West), induct on $|V|$ and choose $X$ maximizing $\operatorname{def}_G(X)$ and, among maximizers, with $|X|$ largest. Maximality of $|X|$ forces every component of $G - X$ to be odd (moving a vertex of an even component into $X$ would not lower the deficiency) and factor-critical (if $K - v$ had no perfect matching, induction gives $Y \subseteq K - v$ with $o(K - v - Y) \ge |Y| + 2$, and $X \cup \{v\} \cup Y$ would be a larger maximizer). If some $S \subseteq X$ had neighbours in fewer than $|S|$ odd components, then $X \setminus S$ would have larger deficiency, so by Hall's theorem (the Konig min-max) $X$ can be matched into distinct odd components; adding near-perfect matchings of all odd components yields a matching that misses exactly $\operatorname{def}_G(X)$ vertices.

## Depends on

- [Odd components and the Tutte deficiency of a vertex set](odd-components-and-tutte-deficiency.md)
- [Factor-critical graphs and near-perfect matchings](factor-critical-graphs.md)

## Proof depends on

- [Every vertex set bounds the matching number through its odd components](odd-components-bound-matching-number.md)
- [Kőnig's theorem for finite bipartite graphs](../k-nig-s-theorem/konig-matching-cover.md)

## Sources

- W. T. Tutte, "The factorization of linear graphs", Journal of the London Mathematical Society 22 (1947).
- C. Berge, "Sur le couplage maximum d'un graphe", Comptes Rendus de l'Academie des Sciences Paris 247 (1958).
- D. B. West, "A short proof of the Berge-Tutte Formula and the Gallai-Edmonds Structure Theorem", European Journal of Combinatorics 32 (2011).
