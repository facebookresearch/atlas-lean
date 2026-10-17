---
article_id: af_3477324d76642b2f63a7f913
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: thm_2_6_sparse_ls_high_prob
---

# Theorem 2.6

Fix a positive integer $k \leq d/2$. Let $K = \mathcal{B}_0(k)$ be the set of $k$-sparse vectors of $\mathbb{R}^d$ and assume that $\theta^* \in \mathcal{B}_0(k)$. Moreover, assume the conditions of Theorem 2.2. Then, for any $\delta > 0$, with probability $1 - \delta$, it holds $$\mathsf{MSE}(\mathbb{X}\hat{\theta}_{\mathcal{B}_0(k)}^{\mathrm{LS}}) \lesssim \frac{\sigma^2}{n} \log \binom{d}{2k} + \frac{\sigma^2 k}{n} + \frac{\sigma^2}{n} \log(1/\delta).$$

## Depends on

- [Theorem 2.2](021-theorem-2-2.md)

## Proof depends on

- [Definition 1.17](../section-1/017-definition-1-17.md)
- [Lemma 1.18](../section-1/018-lemma-1-18.md)
- [Theorem 1.19](../section-1/019-theorem-1-19.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 2, Section 2.2](../../../../sources/v1/HighDimensionalStatistics.md)
