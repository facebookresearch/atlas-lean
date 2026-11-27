# Exact per-SNP mixed-model association by eigen-rotation of the relatedness matrix

Let $y \in \mathbb{R}^n$ be phenotypes, $W \in \mathbb{R}^{n \times c}$ covariates (including an intercept), $x \in \mathbb{R}^n$ the genotypes of the SNP under test, and $K$ a known symmetric positive semidefinite $n \times n$ relatedness matrix. The linear mixed model is

$$y = W\alpha + x\beta + u + \varepsilon, \qquad u \sim \mathcal{N}_n(0, \lambda\tau^{-1} K), \qquad \varepsilon \sim \mathcal{N}_n(0, \tau^{-1} I_n),$$

with $u$ and $\varepsilon$ independent, residual precision $\tau > 0$ and variance ratio $\lambda \ge 0$. Write the eigendecomposition $K = U D U^{\top}$ with $U$ orthogonal and $D = \operatorname{diag}(d_1, \dots, d_n)$, and put $\tilde y = U^{\top} y$, $\tilde W = U^{\top} W$, $\tilde x = U^{\top} x$.

**Proposition (rotation; Zhou and Stephens 2012).** The rotated data satisfy $\tilde y = \tilde W\alpha + \tilde x \beta + \tilde e$ with $\tilde e \sim \mathcal{N}_n\big(0, \tau^{-1}(\lambda D + I_n)\big)$, a diagonal covariance. Hence the log-likelihood is

$$\ell(\lambda, \alpha, \beta, \tau) = \frac n2 \log\frac{\tau}{2\pi} - \frac12 \sum_{i=1}^{n} \log(\lambda d_i + 1) - \frac\tau2 \sum_{i=1}^{n} \frac{(\tilde y_i - \tilde W_{i\cdot}\alpha - \tilde x_i\beta)^2}{\lambda d_i + 1}.$$

For fixed $\lambda$, the maximizers $(\hat\alpha, \hat\beta)$ are the weighted least-squares estimates with weights $(\lambda d_i + 1)^{-1}$ and $\hat\tau^{-1}$ is the weighted mean squared residual, so the profile log-likelihood (and the REML criterion) in $\lambda$, together with its first and second derivatives, costs $O(n c^2)$ per evaluation. Consequently, after one $O(n^3)$ eigendecomposition of $K$ shared by all SNPs, each SNP needs one $O(n^2)$ product $U^{\top}x$ plus $O(n)$-per-iteration Newton–Raphson optimization of $\lambda$, and yields the **exact** Wald or likelihood-ratio statistic for $H_0 : \beta = 0$ with $\lambda$ re-estimated for that SNP. Total cost for $p$ SNPs is $O(n^3 + p n^2 + p t c^2 n)$ for $t$ iterations, versus an extra eigendecomposition per SNP in earlier exact methods.

## Depends on

- [Orthonormal error contrasts rotate to diagonalize a symmetric matrix](../greml-and-haseman-elston-estimation-of-snp-herit/exists-is-spectral-contrast.md)
- [Generalized least-squares estimator](../bolt-lmm-mixed-model-association/gls.md)

## Expansion

The marginal covariance of $y$ is $\tau^{-1}(\lambda K + I_n) = \tau^{-1} U(\lambda D + I_n)U^{\top}$, and an orthogonal change of coordinates preserves Gaussianity and the determinant up to the factor $\prod_i (\lambda d_i + 1)$, giving the displayed likelihood. Because the rotation $U$ depends only on $K$, not on the tested SNP or on $\lambda$, it is computed once; the per-SNP work reduces to rotating the new column $x$ and solving a diagonal-weighted least-squares problem for each trial $\lambda$. This is what makes exact per-SNP variance-component re-estimation, rather than fixing $\lambda$ at its null value as in approximate methods, affordable genome-wide.

## Sources

- X. Zhou and M. Stephens, "Genome-wide efficient mixed-model analysis for association studies", Nature Genetics 44 (2012), 821–824, Results and Table 1, <https://doi.org/10.1038/ng.2310> (PMC3386377).
