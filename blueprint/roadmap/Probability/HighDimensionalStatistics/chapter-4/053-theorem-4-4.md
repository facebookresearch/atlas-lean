---
article_id: af_ef447c2005c828a08bcb0711
declaration: theorem
origin: cited
statement: formalized
lean: Rigollet.Chapter4.Thm_4_4.theorem_4_4_with_probability
---

# Theorem 4.4

Consider the multivariate linear regression model (4.1). Then, the estimator by rank penalization $\hat{\Theta}^{\mathrm{RK}}$ with regularization parameter $\tau^2$, where $\tau$ is defined in (4.3) satisfies $$\frac{1}{n} \|\mathbb{X}\hat{\Theta}^{\mathrm{RK}} - \mathbb{X}\Theta^*\|_F^2 \leq 8 \operatorname{rank}(\Theta^*) \tau^2 \lesssim \frac{\sigma^2 \operatorname{rank}(\Theta^*)}{n} \left( d \vee T + \log(1/\delta) \right)$$ with probability $1 - \delta$.

## Depends on

- [Theorem 4.3](052-theorem-4-3.md)

## Proof depends on

- [Definition 1.2](../chapter-1/002-definition-1-2.md)
- [Lemma 4.2](051-lemma-4-2.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 4](../../../../sources/v1/HighDimensionalStatistics.md)
