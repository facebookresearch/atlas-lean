# Fixed column hooks of size $k$ in odd distinct partitions, even column

Let $n$, $m$ and
$k \ge 1$ be natural numbers with $m \ge 1$ even, and let $h < k$ be an integer.
For a partition $\lambda$, write $\lambda_r$ for its $r$-th largest part ($0$ if it has fewer
than $r$ parts), $\lambda'_m$ for the number of its parts that are at least $m$, and
$h_{r,m}(\lambda) = \lambda_r + \lambda'_m - r - m + 1$ for the hook length of the square $(r, m)$.
The partition $\lambda$ has an $h$-fixed hook in column $m$ at row $r$ when $r \ge 1$,
$m \le \lambda_r$ and $h_{r,m}(\lambda) = r + h$.
The number of partitions $\lambda$ of $n$ into distinct odd parts that have an $h$-fixed hook in
column $m$ at some row $r \le n$ with $h_{r,m}(\lambda) = k$ equals the coefficient of $q^n$ in

$$
\sum_{l} q^{k - l + (m-1)(2k-h-l) + k + l(k-h-1) + 2\binom{k-h}{2} + 2\binom{k-l}{2}}
\frac{(-q;q^2)_{m/2}}{(q^2;q^2)_{k-h-1}} \binom{k - l + (3l-2k-2)/2}{k-l}_{q^2},
$$

the sum running over the even $l$ with $\lceil 2k/3 \rceil \le l \le k$, where
$(q^2;q^2)_j = \prod_{i=1}^{j} (1 - q^{2i})$, $(-q;q^2)_j = \prod_{i=0}^{j-1} (1 + q^{2i+1})$
and $\binom{a}{b}_{q^2}$ is the Gaussian binomial coefficient in $q^2$.

On the range of summation the top index $k - l + (3l-2k-2)/2 = (l-2)/2$ is a nonnegative
integer. Only even $m$ is stated: for odd $m$ the source prints the top index
$k - l + (3l-2k)/2$ over odd $l$, which is not an integer.

## Sources

- Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25 (2025), Article A28, Theorem 14 (`integers-2025-A28-thm-14`), even `m`.
