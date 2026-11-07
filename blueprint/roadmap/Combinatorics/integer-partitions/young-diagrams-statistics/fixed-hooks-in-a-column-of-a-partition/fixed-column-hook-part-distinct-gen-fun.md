# Fixed column hooks from a part of size $k$ in distinct partitions

Let $n$, $m \ge 1$
and $k \ge m$ be natural numbers and let $h$ be an integer with $h + m \le k$.
For a partition $\lambda$, write $\lambda_r$ for its $r$-th largest part ($0$ if it has fewer
than $r$ parts), $\lambda'_m$ for the number of its parts that are at least $m$, and
$h_{r,m}(\lambda) = \lambda_r + \lambda'_m - r - m + 1$ for the hook length of the square $(r, m)$.
The partition $\lambda$ has an $h$-fixed hook in column $m$ at row $r$ when $r \ge 1$,
$m \le \lambda_r$ and $h_{r,m}(\lambda) = r + h$.
The number of partitions $\lambda$ of $n$ into distinct parts that have an $h$-fixed hook in
column $m$ at some row $r \le n$ with $\lambda_r = k$ equals the coefficient of $q^n$ in

$$
\sum_{s=0}^{k-m} q^{s(k+m) + k(k-h-m+1) + \binom{s+k-m+1-h}{2} + \binom{s}{2}}
\frac{(-q;q)_{m-1}}{(q;q)_{s+k-h-m}} \binom{k-m}{s}_q,
$$

where $(q;q)_j = \prod_{i=1}^{j} (1 - q^i)$, $(-q;q)_j = \prod_{i=1}^{j} (1 + q^i)$ and
$\binom{a}{b}_q$ is the Gaussian binomial coefficient.

The denominator $(q;q)_{s+k-h-m}$ follows the journal version. The arXiv version
(arXiv:2406.08609) prints $(q;q)_{k-h-1}$, which is false: for $m = 1$, $k = 2$, $h = 0$ the
number of such partitions of $12$ is $3$, but the coefficient of $q^{12}$ is $2$.

## Sources

- Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25 (2025), Article A28, Theorem 9 (`integers-2025-A28-thm-9`).
