# Overlap statistic on pairs of weakly decreasing words

Fix natural numbers $k$, $n \ge 1$,
$r \ge 1$ and a rational number $q$, and order an alphabet of $k$ letters. For words $u$ and $v$
over this alphabet, the overlap of $(u, v)$ is the number of positions of $v$ whose letter occurs
in $u$. Write $[x^m] F$ for the coefficient of $x^m$ in a formal power series $F$ over
$\mathbb{Q}$. Let $T$ be the sum of $q^{\text{overlap}}$ over all pairs $(u, v)$ of weakly
decreasing words, $u$ of length $n$ and $v$ of length $r$. Then
$T = \sum_{j=1}^{k} \binom{k}{j} \, [x^n]\bigl(x^j (1-x)^{-j}\bigr) \,
[x^r]\Bigl((1-x)^{-(k-j)} - 1 + (1-x)^{-(k-j)} \sum_{m \ge 1} \binom{m+j-1}{m} q^m x^m\Bigr)$
and
$T = \sum_{j=1}^{k} \binom{k}{j} \, [x^n]\bigl(x^j (1-x)^{-j}\bigr) \,
[x^r]\bigl(-1 + (1-x)^{-(k-j)} (1 - qx)^{-j}\bigr)$.

The paper prints these sums over $j$ with upper limit $k - 1$, which omits the pairs whose first
word uses all $k$ letters ($j = k$, which Theorem 2 includes): for $k = 1$ and $n = r = 1$ the
only pair contributes $q$, while the printed sum is empty.

## Sources

- Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024), Article A107, Theorem 4 (`integers-2024-A107-thm-4`).
