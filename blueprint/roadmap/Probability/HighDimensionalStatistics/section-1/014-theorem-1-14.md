---
article_id: af_28f9117f47c17a84e2d0a1f5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: subGaussian_maximal_inequality
---

# Theorem 1.14

Let $X_1, \ldots, X_N$ be $N$ random variables such that $X_i \sim \mathsf{subG}(\sigma^2)$. Then $$\mathbb{E}\!\left[\max_{1 \leq i \leq N} X_i\right] \leq \sigma \sqrt{2 \log(N)}, \quad \text{and} \quad \mathbb{E}\!\left[\max_{1 \leq i \leq N} |X_i|\right] \leq \sigma \sqrt{2 \log(2N)}.$$ Moreover, for any $t > 0$, $$\mathbb{P}\!\left(\max_{1 \leq i \leq N} X_i > t\right) \leq N e^{-t^2/(2\sigma^2)}, \quad \text{and} \quad \mathbb{P}\!\left(\max_{1 \leq i \leq N} |X_i| > t\right) \leq 2N e^{-t^2/(2\sigma^2)}.$$ Note that the random variables in this theorem need not be independent.

## Depends on

- [Definition 1.2](../chapter-1/002-definition-1-2.md)

## Proof depends on

- [Lemma 1.3](003-lemma-1-3.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Section 1.4](../../../../sources/v1/HighDimensionalStatistics.md)
