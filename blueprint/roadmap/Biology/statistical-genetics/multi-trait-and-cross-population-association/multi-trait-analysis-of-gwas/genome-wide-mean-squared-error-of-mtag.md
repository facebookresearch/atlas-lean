# Genome-wide mean squared error of MTAG

In the setting of the [MTAG estimator](mtag-estimator.md), let $\Omega$ now denote the across-SNP covariance of the true effects (no homogeneity across SNPs is assumed), and let $a=\omega_t/\omega_{tt}$ and $W_t=(\Omega-\omega_t\omega_t^\top/\omega_{tt}+\Sigma_j)^{-1}$. Because the true effects and the MTAG estimates both have mean zero across SNPs, the genome-wide mean squared error equals the sampling variance:

$$\mathrm{MSE}\bigl(\hat\beta_{\mathrm{MTAG},j,t}\bigr)=E\bigl[(\hat\beta_{\mathrm{MTAG},j,t}-\beta_{j,t})^2\bigr]=\bigl(a^\top W_ta\bigr)^{-1}.$$

It never exceeds the mean squared error of the single-trait GWAS estimate:

$$\bigl(a^\top W_ta\bigr)^{-1}\le\Sigma_{j,tt}=E(\varepsilon_{j,t}^2)=\mathrm{MSE}(\hat\beta_{j,t}).$$

## Depends on

- [MTAG estimator](mtag-estimator.md)

## Expansion

A short proof of the inequality: let $e_t$ be the $t$-th standard basis vector. Then $a^\top e_t=\omega_{tt}/\omega_{tt}=1$, and $e_t^\top W_t^{-1}e_t=\omega_{tt}-\omega_{tt}^2/\omega_{tt}+\Sigma_{j,tt}=\Sigma_{j,tt}$. Since $W_t$ is positive definite, the Cauchy–Schwarz inequality in the inner products defined by $W_t$ and $W_t^{-1}$ gives $1=(a^\top e_t)^2\le(a^\top W_ta)(e_t^\top W_t^{-1}e_t)=(a^\top W_ta)\,\Sigma_{j,tt}$, which rearranges to the claim. Equality holds when $W_ta$ is parallel to $e_t$, for example when $\Omega$ and $\Sigma_j$ are both diagonal. Lower genome-wide MSE is why MTAG-based polygenic predictors tend to beat GWAS-based ones even where individual MTAG estimates are biased.

## Sources

- P. Turley, R. K. Walters, O. Maghzian et al., *Multi-trait analysis of genome-wide association summary statistics using MTAG*, Nature Genetics 50 (2018), 229–237, <https://doi.org/10.1038/s41588-017-0009-4> (PMCID: PMC5805593). Online Methods, "MTAG's Genome-Wide Mean Squared Error (MSE)"; the inequality is proved in the Supplementary Note, and the Cauchy–Schwarz argument in the Expansion is a self-contained derivation of it.
