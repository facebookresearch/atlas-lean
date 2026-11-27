# Non-intersecting pairs of words

Fix natural numbers $k$, $n \ge 1$ and $r \ge 1$, and call
a pair of words over an alphabet of $k$ letters non-intersecting when no letter occurs in both.
Write $[x^m] F$ for the coefficient of $x^m$ in a formal power series $F$ over $\mathbb{Q}$ and
$S(m, j)$ for the Stirling numbers of the second kind. Let $N$ be the number of non-intersecting
pairs $(u, v)$ with $u$ of length $n$ and $v$ of length $r$. Then
$N = \sum_{j=1}^{k-1} \binom{k}{j} \,
[x^n]\Bigl(j! \, x^j \bigl(\prod_{i=1}^{j} (1 - i x)\bigr)^{-1}\Bigr) \,
[x^r]\bigl((k-j) x \, (1 - (k-j) x)^{-1}\bigr)$
and
$N = \sum_{j=1}^{k-1} \binom{k}{j} \, j! \, S(n, j) \,
[x^r]\bigl((k-j) x \, (1 - (k-j) x)^{-1}\bigr)$.

## Sources

- Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024), Article A107, Theorem 1.
