# Logistic mixed-model score test with multiple variance components

Let $n$ individuals have binary phenotypes $y_i\in\{0,1\}$, covariate rows $X_i\in\mathbb{R}^{1\times p}$ (including an intercept) and genotypes $G_i$ at a tested variant. The logistic mixed model is

$$\operatorname{logit}(\pi_i)=X_i\alpha+G_i\beta+b_i,\qquad b\sim N\Bigl(0,\sum_{k=1}^K\tau_kV_k\Bigr),$$

where $\pi_i=\Pr(y_i=1\mid X_i,G_i,b_i)$, the $y_i$ are conditionally independent given $b$, and $V_1,\dots,V_K$ are known $n\times n$ relatedness matrices (for example a genetic relationship matrix plus household and sampling-cluster indicator matrices). Fit the null model $\operatorname{logit}(\pi_{i0})=X_i\alpha+b_i$ once, by penalized quasi-likelihood: with $v_{i0}=\pi_{i0}(1-\pi_{i0})$, $W=\operatorname{diag}\{v_{i0}\}$ and working vector $\tilde Y_i=X_i\alpha+b_i+v_{i0}^{-1}(y_i-\pi_{i0})$, iterate the working linear mixed model

$$\tilde Y=X\alpha+b+\varepsilon,\qquad \varepsilon\sim N(0,W^{-1}),$$

estimating $\tau_1,\dots,\tau_K$ by AI-REML and updating $\hat\alpha$, $\hat b$ and $\tilde Y$ until convergence. With $\hat\Sigma=\hat W^{-1}+\sum_k\hat\tau_kV_k$ and

$$\hat P=\hat\Sigma^{-1}-\hat\Sigma^{-1}X(X^\top\hat\Sigma^{-1}X)^{-1}X^\top\hat\Sigma^{-1},$$

the score statistic for $H_0:\beta=0$ and its null variance are

$$T=G^\top(y-\hat\pi_0),\qquad \widehat{\operatorname{Var}}(T\mid H_0)=G^\top\hat PG,$$

and $T^2/(G^\top\hat PG)$ is referred to $\chi^2_1$. The null fit is shared by all variants, so each additional variant costs one quadratic form, $O(n^2)$.

## Expansion

Penalized quasi-likelihood linearizes the logit link around the current fit, so each iteration is a linear mixed model with heteroscedastic residual variance $W^{-1}$; this is what lets binary traits keep the right mean–variance relation, unlike a linear mixed model applied directly to 0/1 outcomes, whose residual variance cannot depend on the fitted probability. $\hat P$ is the REML projection that removes the fixed covariates, so $G^\top\hat PG$ is the variance of the covariate-adjusted score. Multiple components let the model absorb population structure, cryptic relatedness and shared environment at once. SAIGE later replaces the exact quadratic form $G^\top\hat PG$ by a variance-ratio approximation to scale to biobanks.

## Sources

- H. Chen, C. Wang, M. P. Conomos et al., *Control for population structure and relatedness for binary traits in genetic association studies via logistic mixed models*, The American Journal of Human Genetics 98 (2016), 653–666, <https://doi.org/10.1016/j.ajhg.2016.02.012> (PMCID: PMC4833218). Material and Methods, "Logistic Mixed Models and Score Tests" (Equation 1 and the score-test formulas), and Appendix A.
