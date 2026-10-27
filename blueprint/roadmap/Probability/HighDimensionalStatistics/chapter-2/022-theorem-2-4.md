---
article_id: af_90694862635104da98432f1b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Rigollet.Chapter2.thm_2_4_l1_ball_mse
---

# Theorem 2.4

Let $K = \mathcal{B}_1$ be the unit $\ell_1$ ball of $\mathbb{R}^d$, $d \geq 2$ and assume that $\theta^* \in \mathcal{B}_1$. Moreover, assume the conditions of Theorem 2.2 and that the columns of $\mathbb{X}$ are normalized in such a way that $\max_j |\mathbb{X}_j|_2 \leq \sqrt{n}$. Then the constrained least squares estimator $\hat{\theta}_{\mathcal{B}_1}^{\mathrm{LS}}$ satisfies $$\mathbb{E}\!\left[\mathsf{MSE}(\mathbb{X}\hat{\theta}_{\mathcal{B}_1}^{\mathrm{LS}})\right] = \frac{1}{n}\mathbb{E}|\mathbb{X}\hat{\theta}_{\mathcal{B}_1}^{\mathrm{LS}} - \mathbb{X}\theta^*|_2^2 \lesssim \sigma\sqrt{\frac{\log d}{n}}.$$ Moreover, for any $\delta > 0$, with probability $1 - \delta$, it holds $$\mathsf{MSE}(\mathbb{X}\hat{\theta}^{\mathrm{LS}}_{\mathcal{B}_1}) \lesssim \sigma \sqrt{\frac{\log(d/\delta)}{n}}.$$

## Depends on

- [Definition 1.2](../chapter-1/002-definition-1-2.md)
- [Theorem 2.2](021-theorem-2-2.md)

## Proof depends on

- [Theorem 1.6](../section-1/006-theorem-1-6.md)
- [Theorem 1.16](../section-1/016-theorem-1-16.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 2, Section 2.2](../../../../sources/v1/HighDimensionalStatistics.md)
