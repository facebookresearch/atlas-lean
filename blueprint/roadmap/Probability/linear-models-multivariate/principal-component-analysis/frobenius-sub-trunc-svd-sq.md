# Frobenius error of the truncated SVD

Let $A$ be a real $m \times n$ matrix with singular values $\sigma_0 \ge \sigma_1 \ge \dots$ (with $\sigma_i = 0$ for $i \ge \min(m, n)$), and $\|\cdot\|$ the Frobenius norm. For every $k \in \mathbb{N}$, the [truncated SVD](trunc-svd.md) $A_k$ satisfies

$$\|A - A_k\|^2 = \sum_{k \le i < n} \sigma_i^2,$$

the sum of the discarded squared singular values.

## Sources

- C. Eckart and G. Young, *The approximation of one matrix by another of lower rank*, Psychometrika 1 (1936), 211–218.
