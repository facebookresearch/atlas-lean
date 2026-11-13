# Broder's alternating expansion of the r-Stirling numbers of the first kind

Let $n$, $m$
and $r$ be natural numbers with $1 \le r \le n$. Write $[n, m]_r$ for the unsigned $r$-Stirling
number of the first kind, $[a, b]$ for the unsigned Stirling number of the first kind and
$\lbrace a, b \rbrace$ for the Stirling number of the second kind. Then, in the integers,

$$(-1)^r [n, m]_r = \sum_{k=r}^{n+r-m} [n, m+k-r] \, \lbrace k-1, r-1 \rbrace \, (-1)^k.$$

Broder's Equation (43) sums over all $k$; every term outside the range above vanishes, since
$\lbrace k-1, r-1 \rbrace$ vanishes for $k < r$ and $[n, m+k-r]$ vanishes for $k > n + r - m$.

## Sources

- A. Z. Broder, "The r-Stirling numbers", Stanford Computer Science Report STAN-CS-82-949 (December 1982), PDF page 16 / printed page 13, Equation (43); journal version: Discrete Mathematics 49 (1984), 241-259, DOI 10.1016/0012-365X(84)90161-4.
