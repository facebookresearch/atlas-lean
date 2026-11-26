# Generalized inverse-variance-weighted estimator for correlated instruments

Let $\hat\beta_X,\hat\beta_Y\in\mathbb{R}^K$ be the summarized associations of $K$ variants with a risk factor and an outcome, $\sigma_{Yk}$ the outcome standard errors, and $\rho_{k_1k_2}$ the correlation between variants $k_1$ and $k_2$ ($\rho_{kk}=1$). Put $\Omega_{k_1k_2}=\sigma_{Yk_1}\sigma_{Yk_2}\rho_{k_1k_2}$ and assume $\Omega$ is invertible and $\hat\beta_X\ne0$. The generalized weighted linear regression of $\hat\beta_Y$ on $\hat\beta_X$ through the origin gives

$$\hat\beta_{SSc}=\bigl(\hat\beta_X^\top\Omega^{-1}\hat\beta_X\bigr)^{-1}\hat\beta_X^\top\Omega^{-1}\hat\beta_Y,\qquad \operatorname{se}(\hat\beta_{SSc})=\bigl(\hat\beta_X^\top\Omega^{-1}\hat\beta_X\bigr)^{-1/2}.$$

When the variants are uncorrelated ($\Omega$ diagonal), $\hat\beta_{SSc}$ is the ordinary [inverse-variance-weighted estimator](ivw.md); with correlated variants the uncorrected IVW formula is no longer an estimate of the causal effect.

**Test equivalence with the allele score.** With correlated variants, the leading-order standard errors of the [summarized-data allele score estimator](summarized-data-allele-score-estimator.md) with weights $w$, and of the uncorrected IVW ratio, are

$$\operatorname{se}(\hat\beta_{SSw})=\frac{\bigl(\sum_{k_1,k_2}\rho_{k_1k_2}w_{k_1}w_{k_2}\sigma_{Yk_1}^{-1}\sigma_{Yk_2}^{-1}\bigr)^{1/2}}{\bigl|\sum_kw_k\hat\beta_{Xk}\sigma_{Yk}^{-2}\bigr|},\qquad \operatorname{se}(\hat\beta_{SSt})=\frac{\bigl(\sum_{k_1,k_2}\rho_{k_1k_2}\hat\beta_{Xk_1}\hat\beta_{Xk_2}\sigma_{Yk_1}^{-1}\sigma_{Yk_2}^{-1}\bigr)^{1/2}}{\sum_k\hat\beta_{Xk}^2\sigma_{Yk}^{-2}},$$

and for $w_k=\hat\beta_{Xk}$ the two test statistics $\hat\beta_{SSt}/\operatorname{se}(\hat\beta_{SSt})$ and $\hat\beta_{SSw}/\operatorname{se}(\hat\beta_{SSw})$ coincide, so the two methods reject the causal null together.

## Depends on

- [Inverse-variance-weighted estimator](ivw.md)
- [Summarized-data allele score estimator](summarized-data-allele-score-estimator.md)
## Expansion

$\hat\beta_{SSc}$ is the generalized least-squares solution of $\hat\beta_Y=\beta\hat\beta_X+e$ with $\operatorname{Var}(e)=\Omega$, treating $\hat\beta_X$ as fixed; its variance is $(\hat\beta_X^\top\Omega^{-1}\hat\beta_X)^{-1}$. For the test equivalence, $w=\hat\beta_X$ makes the allele score estimate equal the IVW ratio, and the two standard-error expressions then have the same numerator and the same denominator, so the ratios agree.

## Sources

- S. Burgess, F. Dudbridge, S. G. Thompson, *Combining information on multiple instrumental variables in Mendelian randomization: comparison of allele score and summarized data methods*, Statistics in Medicine (2016), <https://doi.org/10.1002/sim.6835> (PMCID: PMC4832315). Section 4.1, equation (8), and Section 4.2, equations (9)–(11).
