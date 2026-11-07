# Generating function for fixed column hooks from a part of size $k$

Let $n$, $m \ge 1$
and $k \ge m$ be natural numbers and let $h$ be an integer with $h + m \le k$.
For a partition $\lambda$, write $\lambda_r$ for its $r$-th largest part ($0$ if it has fewer
than $r$ parts), $\lambda'_m$ for the number of its parts that are at least $m$, and
$h_{r,m}(\lambda) = \lambda_r + \lambda'_m - r - m + 1$ for the hook length of the square $(r, m)$.
The partition $\lambda$ has an $h$-fixed hook in column $m$ at row $r$ when $r \ge 1$,
$m \le \lambda_r$ and $h_{r,m}(\lambda) = r + h$.
The number of partitions $\lambda$ of $n$ that have an $h$-fixed hook in column $m$ at some row
$r \le n$ with $\lambda_r = k$ equals the coefficient of $q^n$ in

$$
\sum_{s=0}^{n} \frac{q^{s(k+m) + k(k-h-m+1)}}{(q;q)_{s+k-h-m} (q;q)_{m-1}}
\binom{s+k-m}{k-m}_q,
$$

where $(q;q)_j = \prod_{i=1}^{j} (1 - q^i)$ and $\binom{a}{b}_q$ is the Gaussian binomial
coefficient.

The $s$-th term has no monomial below $q^s$, so this is also the coefficient of $q^n$ in the
sum over all $s \ge 0$. The $s$-th term of that sum is the term with index $s + k - h - m + 1$
of the source's first form

$$
\sum_{s \ge k-h-m+1} \frac{q^{s(k+m) + m(h-k+m-1)}}{(q;q)_{s-1} (q;q)_{m-1}}
\binom{s+h-1}{k-m}_q,
$$

whose lower limit $k - h - m + 1$ is a positive row index.

## Sources

- Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25 (2025), Article A28, Theorem 7 (`integers-2025-A28-thm-7`).
