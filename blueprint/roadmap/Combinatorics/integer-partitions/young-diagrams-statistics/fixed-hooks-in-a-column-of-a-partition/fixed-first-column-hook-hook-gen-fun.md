# Partitions with a fixed first-column hook of given size

Let $n$ and $k$ be natural numbers
with $k \ge 1$ and let $h < k$ be an integer. The number of partitions $\lambda$ of $n$ that have an
$h$-fixed hook in column $1$ at some row $s$ whose hook length is $h_{s,1}(\lambda) = k$ is the
coefficient of $q^n$ in

$$\sum_{l=1}^{k} \frac{q^{k+l(k-h-1)}}{(q;q)_{k-h-1}} \binom{k-1}{l-1}_q,$$

where $(q;q)_j = \prod_{i\lt j} (1 - q^{i+1})$ is the finite $q$-Pochhammer symbol and
$\binom{a}{b}_q$ is the Gaussian binomial coefficient.

Such a hook sits in row $s = k - h \ge 1$.

## Sources

- Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25 (2025), Article A28, Theorem 10 (`integers-2025-A28-thm-10`).
