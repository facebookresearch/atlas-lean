# Eckart–Young, best-approximation form

Let $A$ be a real $m \times n$ matrix with singular values $\sigma_0 \ge \sigma_1 \ge \dots$ (with $\sigma_i = 0$ for $i \ge \min(m, n)$), and $\|\cdot\|$ the Frobenius norm. For every $k \in \mathbb{N}$, the least squared Frobenius distance from $A$ to a matrix of rank at most $k$ is

$$\min_{\operatorname{rank} B \le k} \|A - B\|^2 = \sum_{k \le i < n} \sigma_i^2,$$

attained by the [truncated SVD](trunc-svd.md) $A_k$.

## Sources

- C. Eckart and G. Young, *The approximation of one matrix by another of lower rank*, Psychometrika 1 (1936), 211–218.
