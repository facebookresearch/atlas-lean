---
article_id: af_1d1e2318762f0df3488bd299
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: HardThresholding.oracle_bound_and_support_recovery
---

# Theorem 2.11

Consider the linear regression model (2.2) under the assumption ORT or, equivalently, the sub-Gaussian sequence model (2.9). Then the hard thresholding estimator $\hat{\theta}^{\mathrm{HRD}}$ with threshold $2\tau = 2\sigma\sqrt{2 \log(2d/\delta)/n}$ enjoys the following two properties on the same event $A$ such that $\mathbb{P}(A) \geq 1 - \delta$: (i) If $|\theta^*|_0 = k$, $\mathsf{MSE}(\mathbb{X}\hat{\theta}^{\mathrm{HRD}}) = |\hat{\theta}^{\mathrm{HRD}} - \theta^*|_2^2 \lesssim \sigma^2 k \log(2d/\delta)/n$. (ii) If $\min_{j \in \operatorname{supp}(\theta^*)} |\theta^*_j| > 3\tau$, then $\operatorname{supp}(\hat{\theta}^{\mathrm{HRD}}) = \operatorname{supp}(\theta^*)$.

## Depends on

- [Definition 2.10](027-definition-2-10.md)
- [Assumption ORT](../section-2/035-assumption-ort.md)

## Proof depends on

- [Theorem 1.14](../section-1/014-theorem-1-14.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 2, Section 2.3](../../../../sources/v1/HighDimensionalStatistics.md)
