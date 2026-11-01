---
article_id: af_97e769dc9f6144cec88f6570
declaration: theorem
origin: cited
lean: Rigollet.theorem_2_15
---

# Theorem 2.15

Assume that the linear model (2.2) holds where $\varepsilon \sim \mathsf{subG}_n(\sigma^2)$. Moreover, assume that the columns of $\mathbb{X}$ are normalized in such a way that $\max_j |\mathbb{X}_j|_2 \leq \sqrt{n}$. Then, the Lasso estimator $\hat{\theta}^{\mathrm{L}}$ with regularization parameter $2\tau = 2\sigma\sqrt{2 \log(2d)/n} + 2\sigma\sqrt{2 \log(1/\delta)/n}$ satisfies $$\mathsf{MSE}(\mathbb{X}\hat{\theta}^{\mathrm{L}}) = \frac{1}{n}|\mathbb{X}\hat{\theta}^{\mathrm{L}} - \mathbb{X}\theta^*|_2^2 \leq 4|\theta^*|_1 \sigma\sqrt{\frac{2 \log(2d)}{n}} + 4|\theta^*|_1 \sigma\sqrt{\frac{2 \log(1/\delta)}{n}}$$ with probability at least $1 - \delta$. Moreover, there exists a numerical constant $C > 0$ such that $\mathbb{E}[\mathsf{MSE}(\mathbb{X}\hat{\theta}^{\mathrm{L}})] \leq C |\theta^*|_1 \sigma\sqrt{\log(2d)/n}$.

## Depends on

- [Definition 1.2](../chapter-1/002-definition-1-2.md)
- [Definition 2.12](029-definition-2-12.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 2, Section 2.4](../../../../sources/v1/HighDimensionalStatistics.md)
