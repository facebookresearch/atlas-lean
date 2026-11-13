# Fixed hooks in column $m$ arising from parts of size $m$

Let $n$ and $m \ge 1$ be
natural numbers and let $h$ be an integer.
For a partition $\lambda$, write $\lambda_r$ for its $r$-th largest part ($0$ if it has fewer
than $r$ parts), $\lambda'_m$ for the number of its parts that are at least $m$, and
$h_{r,m}(\lambda) = \lambda_r + \lambda'_m - r - m + 1$ for the hook length of the square $(r, m)$.
The partition $\lambda$ has an $h$-fixed hook in column $m$ at row $r$ when $r \ge 1$,
$m \le \lambda_r$ and $h_{r,m}(\lambda) = r + h$.
Count the partitions $\lambda$ of $n$ that have an $h$-fixed hook in column $m$ at some row
$r \le n$ with $\lambda_r = m$. If $n - mh \ge 0$, this number equals the number of partitions of
$n - mh$ in which $m$ occurs as a part exactly once, none of $m + 1, \dots, 2m - 1$ is a part,
and at least $-h$ parts, counted with multiplicity, are at least $2m$. If $n - mh < 0$, the
number is $0$.

## Sources

- Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25 (2025), Article A28, Theorem 2.
