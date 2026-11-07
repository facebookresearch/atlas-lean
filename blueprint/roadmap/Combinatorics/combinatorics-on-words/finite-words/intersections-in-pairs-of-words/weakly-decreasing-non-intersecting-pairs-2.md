# Generating function of non-intersecting pairs of weakly decreasing words

Let $k$ be a
natural number and order an alphabet of $k$ letters. In the ring of formal power series in $x$
and $y$ over $\mathbb{Q}$ let
$f(x, y) = \bigl(x (1-x)^{-1} + (1-y)^{-1}\bigr)^k - (1-x)^{-k} - (1-y)^{-k} + 1$.
Then for all natural numbers $n$ and $r$, the coefficient of $x^n y^r$ in $f$ is $0$ if $n = 0$
or $r = 0$, and otherwise equals the number of pairs $(u, v)$ of weakly decreasing words over this
alphabet, $u$ of length $n$ and $v$ of length $r$, such that no letter occurs in both.

## Sources

- Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024), Article A107, Corollary 4 (`integers-2024-A107-cor-4`).
