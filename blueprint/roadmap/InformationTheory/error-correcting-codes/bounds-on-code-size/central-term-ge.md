# The central binomial term

For $0 < n$ and $0 \le m \le n$, with $x = m/n$,

$$\binom{n}{m} x^m (1 - x)^{n - m} \ge \frac{1}{n + 1}.$$

The terms $t_k = \binom{n}{k} x^k (1-x)^{n-k}$, $0 \le k \le n$, sum to $(x + (1 - x))^n = 1$,
and $t_m$ is the largest: from $\binom{n}{k+1}(k+1) = \binom{n}{k}(n-k)$ the ratio
$t_{k+1}/t_k = \frac{(n-k)\, m}{(k+1)(n-m)}$ is at least $1$ for $k < m$ and at most $1$ for
$k \ge m$.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Proposition 3.3.3 (ii) (where the volume lower bound is derived from Stirling's approximation instead).
