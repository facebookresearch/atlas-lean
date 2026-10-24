---
article_id: af_051b7c06e22e06ab1ea4bfe1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: corollary_1_7_linear_combination_tail
---

# Corollary 1.7

Let $X_1, \ldots, X_n$ be $n$ independent random variables such that $X_i \sim \mathsf{subG}(\sigma^2)$. Then for any $a \in \mathbb{R}^n$, we have $$\mathbb{P}\left[\sum_{i=1}^{n} a_i X_i > t\right] \leq \exp\left(-\frac{t^2}{2\sigma^2 |a|_2^2}\right),$$ and $$\mathbb{P}\left[\sum_{i=1}^{n} a_i X_i < -t\right] \leq \exp\left(-\frac{t^2}{2\sigma^2 |a|_2^2}\right).$$

## Depends on

- [Definition 1.2](../chapter-1/002-definition-1-2.md)

## Proof depends on

- [Theorem 1.6](006-theorem-1-6.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Section 1.2](../../../../sources/v1/HighDimensionalStatistics.md)
