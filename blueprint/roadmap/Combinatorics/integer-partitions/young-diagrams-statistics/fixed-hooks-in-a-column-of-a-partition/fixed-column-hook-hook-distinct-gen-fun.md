# Generating function for fixed column hooks of size $k$ in distinct partitions

Let $n$,
$m \ge 1$ and $k \ge 1$ be natural numbers and let $h < k$ be an integer.
For a partition $\lambda$, write $\lambda_r$ for its $r$-th largest part ($0$ if it has fewer
than $r$ parts), $\lambda'_m$ for the number of its parts that are at least $m$, and
$h_{r,m}(\lambda) = \lambda_r + \lambda'_m - r - m + 1$ for the hook length of the square $(r, m)$.
The partition $\lambda$ has an $h$-fixed hook in column $m$ at row $r$ when $r \ge 1$,
$m \le \lambda_r$ and $h_{r,m}(\lambda) = r + h$.
The number of partitions $\lambda$ of $n$ into distinct parts that have an $h$-fixed hook in
column $m$ at some row $r \le n$ with $h_{r,m}(\lambda) = k$ equals the coefficient of $q^n$ in

$$
\sum_{l=\lceil (k+1)/2 \rceil}^{k}
q^{k + l(k-h-1) + (m-1)(2k-h-l) + \binom{k-h}{2} + \binom{k-l}{2}}
\frac{(-q;q)_{m-1}}{(q;q)_{k-h-1}} \binom{l-1}{k-l}_q,
$$

where $(q;q)_j = \prod_{i=1}^{j} (1 - q^i)$, $(-q;q)_j = \prod_{i=1}^{j} (1 + q^i)$ and
$\binom{a}{b}_q$ is the Gaussian binomial coefficient.

## Sources

- Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25 (2025), Article A28, Theorem 13.
