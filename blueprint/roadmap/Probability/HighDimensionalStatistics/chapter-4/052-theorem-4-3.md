---
article_id: af_37ffe33b5973ee5a91be47e9
declaration: theorem
origin: cited
lean: SingularValueThresholding.theorem_4_3
---

# Theorem 4.3

Consider the multivariate linear regression model (4.1) under the assumption ORT or, equivalently, the sub-Gaussian matrix model (4.2). Then, the singular value thresholding estimator $\hat{\Theta}^{\mathrm{SVT}}$ with threshold $$2\tau = 8\sigma\sqrt{\frac{\log(12)(d \vee T)}{n}} + 4\sigma\sqrt{\frac{2\log(1/\delta)}{n}},$$ satisfies $$\frac{1}{n} \|\mathbb{X}\hat{\Theta}^{\mathrm{SVT}} - \mathbb{X}\Theta^*\|_F^2 = \|\hat{\Theta}^{\mathrm{SVT}} - \Theta^*\|_F^2 \leq 144 \operatorname{rank}(\Theta^*) \tau^2 \lesssim \frac{\sigma^2 \operatorname{rank}(\Theta^*)}{n} \left( d \vee T + \log(1/\delta) \right)$$ with probability $1 - \delta$.

## Depends on

- [Assumption ORT](../section-2/035-assumption-ort.md)
- [Definition 4.1](050-definition-4-1.md)

## Proof depends on

- [Lemma 4.2](051-lemma-4-2.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 4](../../../../sources/v1/HighDimensionalStatistics.md)
