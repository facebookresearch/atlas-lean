# Overlap statistic on pairs of words of equal length

Fix natural numbers $k$ and $n \ge 1$
and a rational number $q$. For words $u$ and $v$ over an alphabet of $k$ letters, the overlap of
$(u, v)$ is the number of positions of $v$ whose letter occurs in $u$. Let $S(n, j)$ denote the
Stirling numbers of the second kind. Then the sum of $q^{\text{overlap}}$ over all pairs $(u, v)$
of words of length $n$ equals $\sum_{j=1}^{k} \binom{k}{j} \, j! \, S(n, j) \, (qj + k - j)^n$.

## Sources

- Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024), Article A107, Corollary 3 (`integers-2024-A107-cor-3`).
