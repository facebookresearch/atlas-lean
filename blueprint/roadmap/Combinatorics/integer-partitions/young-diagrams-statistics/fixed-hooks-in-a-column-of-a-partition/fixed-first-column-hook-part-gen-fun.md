# Partitions with a fixed first-column hook arising from a part of given size

Let $n$ and $k$
be natural numbers with $k \ge 1$ and let $h < k$ be an integer. The number of partitions
$\lambda$ of $n$ that have an $h$-fixed hook in column $1$ at some row $s$ with $\lambda_s = k$ is
the coefficient of $q^n$ in

$$\sum_{s=0}^{n} \frac{q^{s(k+1)+k(k-h)}}{(q;q)_{s+k-h-1}} \binom{s+k-1}{k-1}_q,$$

where $(q;q)_j = \prod_{i\lt j} (1 - q^{i+1})$ is the finite $q$-Pochhammer symbol and
$\binom{a}{b}_q$ is the Gaussian binomial coefficient.

The $s$-th term has no monomial below $q^s$, so the count is also the coefficient of $q^n$ in the
full series over all $s \ge 0$. Under $s \mapsto s + k - h$ that series is the paper's
$\sum_{s \ge k-h} q^{(k+1)(s-1)+h+1} \binom{s+h-1}{k-1}_q / (q;q)_{s-1}$, whose lower limit
$k - h$ is a positive row index.

## Sources

- Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25 (2025), Article A28, Theorem 6 (`integers-2025-A28-thm-6`).
