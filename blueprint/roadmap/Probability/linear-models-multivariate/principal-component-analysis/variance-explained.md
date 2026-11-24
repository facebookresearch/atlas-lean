# Proportion of variance explained by principal components

Let $X$ be a real $n \times p$ data matrix whose rows are observations. Let $S$ be its [sample covariance matrix](sample-cov.md), with ordered eigenvalues $\lambda_0 \ge \dots \ge \lambda_{p-1}$, and $k \in \mathbb{N}$. The proportion of total sample variance explained by the first $k$ principal components is

$$\frac{\lambda_0 + \dots + \lambda_{\min(k,p)-1}}{\operatorname{tr} S},$$

which is $0$ by convention when $\operatorname{tr} S = 0$ (constant data).

## Sources

- I. T. Jolliffe, *Principal Component Analysis*, 2nd ed., Springer, 2002, §§2.1, 3.5.
