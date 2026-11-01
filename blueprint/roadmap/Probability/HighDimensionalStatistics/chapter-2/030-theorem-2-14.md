---
article_id: af_b646971d75c5b64bf45252b5
declaration: theorem
origin: cited
statement: formalized
lean: thm_2_14_probabilistic
---

# Theorem 2.14

Assume that the linear model (2.2) holds where $\varepsilon \sim \mathsf{subG}_n(\sigma^2)$. Then, the BIC estimator $\hat{\theta}^{\mathrm{BIC}}$ with regularization parameter $\tau^2 = 16 \log(6) \sigma^2/n + 32 \sigma^2 \log(ed)/n$ satisfies $$\mathsf{MSE}(\mathbb{X}\hat{\theta}^{\mathrm{BIC}}) = \frac{1}{n}|\mathbb{X}\hat{\theta}^{\mathrm{BIC}} - \mathbb{X}\theta^*|_2^2 \lesssim |\theta^*|_0 \frac{\sigma^2 \log(ed/\delta)}{n}$$ with probability at least $1 - \delta$.

## Depends on

- [Definition 1.2](../chapter-1/002-definition-1-2.md)

## Proof depends on

- [Definition 1.17](../section-1/017-definition-1-17.md)
- [Definition 2.12](029-definition-2-12.md)
- [Lemma 1.18](../section-1/018-lemma-1-18.md)
- [Lemma 2.7](024-lemma-2-7.md)
- [Theorem 1.6](../section-1/006-theorem-1-6.md)
- [Theorem 1.19](../section-1/019-theorem-1-19.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 2, Section 2.4](../../../../sources/v1/HighDimensionalStatistics.md)
