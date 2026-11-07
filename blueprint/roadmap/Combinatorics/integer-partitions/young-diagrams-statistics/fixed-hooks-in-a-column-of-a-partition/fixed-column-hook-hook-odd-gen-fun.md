# Generating function for fixed column hooks of size $k$ in odd partitions

Let $n$,
$m \ge 1$ and $k \ge 1$ be natural numbers and let $h < k$ be an integer.
For a partition $\lambda$, write $\lambda_r$ for its $r$-th largest part ($0$ if it has fewer
than $r$ parts), $\lambda'_m$ for the number of its parts that are at least $m$, and
$h_{r,m}(\lambda) = \lambda_r + \lambda'_m - r - m + 1$ for the hook length of the square $(r, m)$.
The partition $\lambda$ has an $h$-fixed hook in column $m$ at row $r$ when $r \ge 1$,
$m \le \lambda_r$ and $h_{r,m}(\lambda) = r + h$.
In $\mathbb{Q}[[q]]$ write $(q^2;q^2)_j = \prod_{i=1}^{j} (1 - q^{2i})$ and
$(q;q^2)_j = \prod_{i=0}^{j-1} (1 - q^{2i+1})$, and let $\binom{a}{b}_{q^2}$ be the Gaussian
binomial coefficient in $q^2$. Let $N$ be the number of partitions $\lambda$ of $n$ into odd
parts that have an $h$-fixed hook in column $m$ at some row $r \le n$ with
$h_{r,m}(\lambda) = k$. If $m$ is odd, $N$ is the coefficient of $q^n$ in

$$
\sum_{l} \frac{q^{k + l(k-h-1) + (m-1)(2k-h-l)}}{(q^2;q^2)_{k-h-1} (q;q^2)_{(m-1)/2}}
\binom{k-l+(l-1)/2}{k-l}_{q^2},
$$

the sum running over the odd $l$ with $1 \le l \le k$. If $m$ is even, $N$ is the coefficient
of $q^n$ in

$$
\sum_{l} \frac{q^{k + l(k-h-1) + (m-1)(2k-h-l) + (k-l)}}{(q^2;q^2)_{k-h-1} (q;q^2)_{m/2}}
\binom{k-l+(l-2)/2}{k-l}_{q^2},
$$

the sum running over the even $l$ with $1 \le l \le k$.

## Sources

- Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25 (2025), Article A28, Theorem 12 (`integers-2025-A28-thm-12`).
