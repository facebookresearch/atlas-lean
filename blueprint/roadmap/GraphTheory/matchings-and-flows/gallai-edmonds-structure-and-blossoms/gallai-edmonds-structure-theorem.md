# Gallai-Edmonds structure theorem for maximum matchings

Let $G = (V, E)$ be a finite simple graph with Gallai-Edmonds partition $D = D(G)$, $A = A(G)$, $C = C(G)$, and let $k$ be the number of connected components of $G[D]$. Then:

1. every component of $G[D]$ is factor-critical;
2. $G[C]$ has a perfect matching;
3. for every nonempty $S \subseteq A$, the neighbours of $S$ meet at least $|S| + 1$ components of $G[D]$;
4. every maximum matching of $G$ consists of a near-perfect matching of each component of $G[D]$, a perfect matching of $G[C]$, and $|A|$ edges matching $A$ into distinct components of $G[D]$;
5. $\nu(G) = \frac{1}{2}\left(|V| - k + |A|\right)$, so $X = A$ attains the minimum in the Tutte-Berge formula and $\operatorname{def}(G) = k - |A|$.

## Proof sketch

The stability lemma shows that deleting a vertex $a \in A$ lowers $\nu$ by exactly one and leaves $D$ unchanged, $A$ replaced by $A \setminus \{a\}$ and $C$ unchanged; deleting all of $A$ therefore leaves a graph in which every vertex of $D$ is inessential. Each component of $G[D]$ is then a connected graph without essential vertices, hence factor-critical by Gallai's lemma, and $G[C]$ is matched perfectly because its vertices are covered by every maximum matching and have no neighbours in $D$. Counting shows that $X = A$ attains equality in the odd-component bound, which gives (5); equality forces the shape (4) of every maximum matching. Property (3), the positive surplus of $A$ towards the components of $G[D]$, is then derived from (4) together with the stability lemma (Lovász–Plummer, Theorem 3.2.1).

## Depends on

- [The Gallai-Edmonds partition D(G), A(G), C(G)](gallai-edmonds-partition.md)
- [Factor-critical graphs and near-perfect matchings](factor-critical-graphs.md)
- [Odd components and the Tutte deficiency of a vertex set](odd-components-and-tutte-deficiency.md)

## Proof depends on

- [Tutte-Berge min-max formula for the maximum matching size](tutte-berge-min-max-formula.md)
- [Gallai's lemma: connected graphs without essential vertices are factor-critical](gallai-lemma-factor-critical.md)
- [Every vertex set bounds the matching number through its odd components](odd-components-bound-matching-number.md)

## Sources

- T. Gallai, "Neuer Beweis eines Tutte'schen Satzes", Magyar Tud. Akad. Mat. Kutato Int. Kozl. 8 (1963).
- J. Edmonds, "Paths, trees, and flowers", Canadian Journal of Mathematics 17 (1965).
- L. Lovasz, M. D. Plummer, "Matching Theory", Annals of Discrete Mathematics 29, North-Holland (1986).
- D. B. West, "A short proof of the Berge-Tutte Formula and the Gallai-Edmonds Structure Theorem", European Journal of Combinatorics 32 (2011).
