---
article_id: af_17487dc58de2e5d8952ab2c8
declaration: def
origin: cited
statement: formalized
lean: Rigollet.IsBICEstimator
---

# Definition 2.12

Fix $\tau > 0$ and assume the linear regression model (2.2). The BIC estimator of $\theta^*$ is defined by any $\hat{\theta}^{\mathrm{BIC}}$ such that $$\hat{\theta}^{\mathrm{BIC}} \in \operatorname{argmin}_{\theta \in \mathbb{R}^d} \left\{ \frac{1}{n}|Y - \mathbb{X}\theta|_2^2 + \tau^2 |\theta|_0 \right\}.$$ Moreover the Lasso estimator of $\theta^*$ is defined by any $\hat{\theta}^{\mathrm{L}}$ such that $$\hat{\theta}^{\mathrm{L}} \in \operatorname{argmin}_{\theta \in \mathbb{R}^d} \left\{ \frac{1}{n}|Y - \mathbb{X}\theta|_2^2 + 2\tau |\theta|_1 \right\}.$$

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 2, Section 2.4](../../../../sources/v1/HighDimensionalStatistics.md)
