---
article_id: af_94f1671e33b1e4243056fc7f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Thm48.theorem_4_8
---

# Theorem 4.8 (Davis-Kahan $\sin(\theta)$ theorem)

Let $\Sigma$ satisfy the spiked covariance model and let $\tilde{\Sigma}$ be any PSD estimator of $\Sigma$. Let $\tilde{v}$ denote the largest eigenvector of $\tilde{\Sigma}$. Then we have $$\min_{\varepsilon \in \{\pm 1\}} |\varepsilon \tilde{v} - v|_2^2 \leq 2 \sin^2\!\left(\angle(\tilde{v}, v)\right) \leq \frac{8}{\theta^2} \|\tilde{\Sigma} - \Sigma\|_{\mathrm{op}}^2.$$

## Depends on

- [Definition 4.7](055-definition-4-7.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Section 4.4](../../../../sources/v1/HighDimensionalStatistics.md)
