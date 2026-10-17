---
article_id: af_3fdcdc1a69ba8ba7f03b9b0e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: theorem_1_13_bernstein_inequality
---

# Theorem 1.13 (Bernstein's inequality)

Let $X_1, \ldots, X_n$ be independent random variables such that $\mathbb{E}(X_i) = 0$ and $X_i \sim \mathsf{subE}(\lambda)$. Define $\bar{X} = \frac{1}{n} \sum_{i=1}^{n} X_i$. Then for any $t > 0$ we have $$\mathbb{P}(\bar{X} > t) \vee \mathbb{P}(\bar{X} < -t) \leq \exp\left[-\frac{n}{2}\left(\frac{t^2}{\lambda^2} \wedge \frac{t}{\lambda}\right)\right].$$

## Depends on

- [Definition 1.11](011-definition-1-11.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Section 1.3](../../../../sources/v1/HighDimensionalStatistics.md)
