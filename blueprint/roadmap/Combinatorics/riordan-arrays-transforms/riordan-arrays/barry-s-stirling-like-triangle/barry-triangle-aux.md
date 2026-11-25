# Barry's triangle recurrence

The function $s(\beta, n, k)$ of natural numbers
$\beta, n, k$, with natural-number values, is defined by $s(\beta, 0, 0) = 1$, by
$s(\beta, n, k) = 0$ if exactly one of $n, k$ is $0$, and by

$$s(\beta, n, k) = s(\beta + 1, n - 1, k - 1) + \beta k\, s(\beta, n - 1, k)$$

if $n, k \ge 1$.

The triangle OEIS A080416 is $s(0, n, k)$ for $2 \le k \le n$.

## Sources

- Bulat Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of Integer Sequences 29 (2026), Article 26.2.8, equation (1).
