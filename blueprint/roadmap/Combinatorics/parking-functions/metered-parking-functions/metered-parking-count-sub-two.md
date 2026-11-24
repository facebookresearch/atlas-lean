# Closed form for (m-2)-metered parking functions

Let $m, n$ be natural numbers with
$2 < m \le n + 1$. Then the number $\mathrm{mpf}_{m,n}(m-2)$ of $(m-2)$-metered
$(m, n)$-parking functions is

$$(n-m+2)^2 (m-1)^{m-3} + \sum_{k=n-m+3}^{n} \binom{m-2}{n-k} (n-k+1)^{n-k-1} S_k,$$

where

$$S_k = \binom{k+1}{2}(n-m+2)\, k^{m-n+k-3} +
\left(k(n-m+1) - \binom{n-m+2}{2}\right)(k-n+m-1)^{k-n+m-3} +
\sum_{j=n-m+2}^{k-1} \left(jk - \binom{j+1}{2}\right) \binom{m-2-n+k}{k-1-j} (n-m+1)\,
j^{j+m-2-n} (k-j)^{k-j-2}.$$

Every subtraction is nonnegative on the summation ranges except in the exponents of the bases
$n - k + 1$ (at $k = n$) and $k - j$ (at $j = k - 1$), which equal $1$ there, so the formula is
the same with exponents truncated at $0$.

## Sources

- Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*, INTEGERS 25 (2025), Article A73, Theorem 5.
