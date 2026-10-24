---
article_id: af_146abe0ae8650f5248f0f891
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: thm_2_18_lasso_probabilistic
---

# Theorem 2.18

Fix $n \geq 2$. Assume that the linear model (2.2) holds where $\varepsilon \sim \mathsf{subG}_n(\sigma^2)$. Moreover, assume that $|\theta^*|_0 \leq k$ and that $\mathbb{X}$ satisfies assumption $\mathrm{INC}(k)$. Then the Lasso estimator $\hat{\theta}^{\mathrm{L}}$ with regularization parameter $2\tau = 8\sigma\sqrt{\log(2d)/n} + 8\sigma\sqrt{\log(1/\delta)/n}$ satisfies $$\mathsf{MSE}(\mathbb{X}\hat{\theta}^{\mathrm{L}}) = \frac{1}{n}|\mathbb{X}\hat{\theta}^{\mathrm{L}} - \mathbb{X}\theta^*|_2^2 \lesssim \frac{k \sigma^2 \log(2d/\delta)}{n}$$ and $|\hat{\theta}^{\mathrm{L}} - \theta^*|_1 \lesssim k\sigma\sqrt{\log(2d/\delta)/n}$ with probability at least $1 - \delta$. Moreover, $\mathbb{E}[\mathsf{MSE}(\mathbb{X}\hat{\theta}^{\mathrm{L}})] \lesssim k \sigma^2 \log(2d)/n$ and $\mathbb{E}[|\hat{\theta}^{\mathrm{L}} - \theta^*|_1] \lesssim k\sigma\sqrt{\log(2d/\delta)/n}$.

## Depends on

- [Assumption INC(k)](../section-2/036-k.md)
- [Definition 1.2](../chapter-1/002-definition-1-2.md)
- [Definition 2.12](029-definition-2-12.md)

## Proof depends on

- [Lemma 2.17](033-lemma-2-17.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 2, Section 2.4](../../../../sources/v1/HighDimensionalStatistics.md)
