# Generating function of non-intersecting pairs of words of equal length

Let $k$ be a
natural number, let $S(n, j)$ denote the Stirling numbers of the second kind, and for $n \ge 1$ let
$h(n)$ be the number of pairs $(u, v)$ of words of length $n$ over an alphabet of $k$ letters such
that no letter occurs in both. Then, as formal power series over $\mathbb{Q}$,
$\sum_{n \ge 1} h(n) x^n = \sum_{n \ge 0} \sum_{j=1}^{k-1} \binom{k}{j} \, j! \, S(n, j) \,
(k-j)^n x^n$.

The constant term on the right is $0$ because $S(0, j) = 0$ for $j \ge 1$: the empty pair is not
counted.

## Sources

- Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024), Article A107, Corollary 1.
