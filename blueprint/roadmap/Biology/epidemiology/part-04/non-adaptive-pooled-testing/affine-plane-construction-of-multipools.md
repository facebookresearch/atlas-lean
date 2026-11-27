# Affine-plane construction of multipools

Use the definition of an $(N, n, k)$-multipool from [False-positive bound for multipool testing](false-positive-bound-for-multipool-testing.md). Arrange $N = n^2$ samples as $X_{i,j}$ with $i, j \in \{0, \dots, n-1\}$.

**Theorem (prime pool size).** Let $n$ be prime. For $l, m \in \{0,\dots,n-1\}$ define the sloped-line pools

$$P(l, m) = \{ X_{j,\; l + m j \bmod n} : j = 0, \dots, n-1 \},$$

and the column pools $P(l, \infty) = \{X_{l, j} : j = 0, \dots, n-1\}$. Then the $n(n+1)$ pools $\{P(l,m) : l \in \mathbb{Z}_n,\ m \in \mathbb{Z}_n \cup \{\infty\}\}$ form an $(n^2, n, n+1)$-multipool, and keeping the pools of any $k \le n + 1$ slopes gives an $(n^2, n, k)$-multipool.

**Theorem (any $n \ge 2$, multiplicity 3).** For every $n \ge 2$, pooling along rows, columns and the periodically continued diagonals of slope $1$ gives an $(n^2, n, 3)$-multipool.

For example, with $n = 31$ and $N = 961$ samples, multiplicities up to $32$ are available, and at incidence at most $1\%$ a small multiplicity already keeps the false-positive share low while using $31k$ tests instead of $961$.

## Depends on

- [False-positive bound for multipool testing](false-positive-bound-for-multipool-testing.md)

## Expansion

The pools of one slope partition the grid into $n$ parallel lines of $n$ points, so each sample lies in exactly one pool per slope, giving (M1) and (M2). For (M3), two distinct points lie on a common line of slope $m$ iff their difference $(\Delta i, \Delta j)$ satisfies $\Delta j \equiv m\,\Delta i \pmod n$; when $n$ is prime, $\mathbb{Z}_n$ is a field, so for $\Delta i \ne 0$ there is exactly one such slope $m = \Delta j\,(\Delta i)^{-1}$, and for $\Delta i = 0$ only the column slope works. Hence two points share at most one pool, and the construction is the affine plane of order $n$ (the shifted transversal design). For composite $n$, two lines of slopes $m, m'$ meet in one point only if $m - m'$ is invertible modulo $n$; slopes $0, 1, \infty$ always have invertible pairwise differences, which yields the multiplicity-3 design, whereas e.g. for $n = 8$ some pairs of diagonals of other slopes meet in more than one point.

## Sources

- M. Täufer, "Rapid, large-scale, and effective detection of COVID-19 via non-adaptive testing", Journal of Theoretical Biology 506 (2020) 110450, Section 4, Theorems 2 and 3 and Eqs. (4.6)–(4.9), <https://doi.org/10.1016/j.jtbi.2020.110450>, PMCID PMC7428746.
