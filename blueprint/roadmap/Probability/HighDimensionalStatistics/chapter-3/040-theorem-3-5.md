---
article_id: af_8ff8f9ecf300a5c46c12b41f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Rigollet.Chapter3.thm_3_5_lasso_oracle_inequality
---

# Theorem 3.5

Assume the general regression model (3.1) with $\varepsilon \sim \mathsf{subG}_n(\sigma^2)$. Moreover, assume that there exists an integer $k$ such that the matrix $\Phi$ satisfies assumption $\mathrm{INC}(k)$. Then, the Lasso estimator $\hat{\theta}^{\mathrm{L}}$ with regularization parameter $2\tau = 8\sigma\sqrt{2\log(2M)/n} + 8\sigma\sqrt{2\log(1/\delta)/n}$ satisfies for some numerical constant $C$, $$\mathsf{MSE}(\varphi_{\hat{\theta}^{\mathrm{L}}}) \leq \inf_{\theta \in \mathbb{R}^M,\, |\theta|_0 \leq k} \left\{ \frac{1+\alpha}{1-\alpha} \mathsf{MSE}(\varphi_\theta) + \frac{C\sigma^2}{\alpha(1-\alpha)n} |\theta|_0 \log(eM) \right\} + \frac{C\sigma^2}{\alpha(1-\alpha)n} \log(1/\delta)$$ with probability at least $1 - \delta$.

## Depends on

- [Definition 1.2](../chapter-1/002-definition-1-2.md)

## Proof depends on

- [Assumption INC(k)](../section-2/036-k.md)
- [Lemma 2.17](../chapter-2/033-lemma-2-17.md)
- [Theorem 1.6](../section-1/006-theorem-1-6.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 3, Section 3.1](../../../../sources/v1/HighDimensionalStatistics.md)
