# Gallai's lemma: connected graphs without essential vertices are factor-critical

Let $H$ be a connected finite simple graph such that $\nu(H - v) = \nu(H)$ for every vertex $v$ of $H$, i.e. $D(H) = V(H)$. Then $H$ is factor-critical. In particular $|V(H)|$ is odd and $\nu(H) = (|V(H)| - 1)/2$.

## Proof sketch

It suffices to show that every maximum matching misses exactly one vertex, since each vertex is missed by some maximum matching. Suppose a maximum matching $M$ misses two vertices, and choose $M$ and missed vertices $u, w$ with $\operatorname{dist}(u, w)$ minimal; then $\operatorname{dist}(u, w) \ge 2$, so a shortest $u$-$w$ path has an interior vertex $t$, which $M$ covers by the minimality. A maximum matching $N$ missing $t$ is chosen to maximize $|M \cap N|$; examining the alternating components of $M \triangle N$ through $u$, $w$ and $t$ produces a maximum matching missing $t$ and one of $u, w$, contradicting the minimal distance.

## Depends on

- [Factor-critical graphs and near-perfect matchings](factor-critical-graphs.md)
- [The Gallai-Edmonds partition D(G), A(G), C(G)](gallai-edmonds-partition.md)

## Proof depends on

- [Augmenting along a path (Hopcroft–Karp, Lemma 1)](../berge-s-lemma/symm-diff-is-matching.md)

## Sources

- T. Gallai, "Neuer Beweis eines Tutte'schen Satzes", Magyar Tud. Akad. Mat. Kutato Int. Kozl. 8 (1963).
- L. Lovasz, M. D. Plummer, "Matching Theory", Annals of Discrete Mathematics 29, North-Holland (1986).
