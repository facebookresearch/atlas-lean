# MTAG estimator

Let $T$ traits and the genotype of SNP $j$ be standardized. Let $\beta_j\in\mathbb{R}^T$ be the true marginal effects of SNP $j$, modelled as random with $E(\beta_j)=0$ and $\operatorname{Var}(\beta_j)=\Omega$, the same for every SNP (homogeneous-$\Omega$ assumption). Let $\hat\beta_j=\beta_j+\varepsilon_j$ be the GWAS estimates, with estimation error uncorrelated with $\beta_j$ and $\operatorname{Var}(\varepsilon_j)=\Sigma_j$ (off-diagonal entries from sample overlap or shared bias). For trait $t$ let $\omega_t$ be the $t$-th column of $\Omega$ and $\omega_{tt}$ its diagonal entry. The best linear prediction of $\hat\beta_j$ from $\beta_{j,t}$ gives the $T$ moment conditions

$$E\Bigl(\hat\beta_j-\frac{\omega_t}{\omega_{tt}}\beta_{j,t}\Bigr)=0 .$$

The efficient GMM estimator with weight matrix $W_t=\bigl(\Omega-\omega_t\omega_t^\top/\omega_{tt}+\Sigma_j\bigr)^{-1}$ is

$$\hat\beta_{\mathrm{MTAG},j,t}=\frac{\frac{\omega_t^\top}{\omega_{tt}}W_t}{\frac{\omega_t^\top}{\omega_{tt}}W_t\frac{\omega_t}{\omega_{tt}}}\,\hat\beta_j,\qquad \operatorname{Var}\bigl(\hat\beta_{\mathrm{MTAG},j,t}-\beta_{j,t}\bigr)=\Bigl(\frac{\omega_t^\top}{\omega_{tt}}W_t\frac{\omega_t}{\omega_{tt}}\Bigr)^{-1}.$$

In practice $\Sigma_j$ is estimated from univariate and bivariate LD score regression intercepts and $\Omega$ by the moment estimator $\hat\omega_{ts}=\frac1M\sum_{j=1}^M\bigl(\hat\beta_{j,t}\hat\beta_{j,s}-\Sigma_{j,ts}\bigr)$ over $M$ SNPs.

**Special cases.** If all inputs are GWAS of the same trait ($\omega_t\omega_t^\top/\omega_{tt}=\Omega$, $\omega_t/\omega_{tt}=\mathbf 1$), then $\hat\beta_{\mathrm{MTAG},j,t}=\mathbf 1^\top\Sigma_j^{-1}\hat\beta_j/(\mathbf 1^\top\Sigma_j^{-1}\mathbf 1)$, which with diagonal $\Sigma_j$ is inverse-variance-weighted meta-analysis. If both $\Omega$ and $\Sigma_j$ are diagonal, $\hat\beta_{\mathrm{MTAG},j,t}=\hat\beta_{j,t}$.

## Expansion

The GMM objective $(\hat\beta_j-a\beta)^\top W_t(\hat\beta_j-a\beta)$ with $a=\omega_t/\omega_{tt}$ is a weighted least-squares problem in the scalar $\beta$, solved by $a^\top W_t\hat\beta_j/(a^\top W_ta)$. The weight is the inverse of $\operatorname{Var}(\hat\beta_j-a\beta_{j,t})=\Omega-\omega_t\omega_t^\top/\omega_{tt}+\Sigma_j$, the residual variance of $\beta_j$ after projecting on $\beta_{j,t}$ plus estimation error. For a SNP null for trait $t$ but not for a correlated trait, homogeneous-$\Omega$ weighting borrows the other trait's signal and biases the estimate away from zero, which inflates the false discovery rate; the source bounds it by a maxFDR calculation. The LD score intercepts make $\hat\Sigma_j$ absorb stratification and unknown sample overlap, so no further genomic-control correction is applied. For the univariate inputs see [LD score regression](../../ld-score-regression/README.md).

## Sources

- P. Turley, R. K. Walters, O. Maghzian et al., *Multi-trait analysis of genome-wide association summary statistics using MTAG*, Nature Genetics 50 (2018), 229–237, <https://doi.org/10.1038/s41588-017-0009-4> (PMCID: PMC5805593). "MTAG Framework" (equation (1)), "Estimation of $\Sigma_j$" and "Estimation of $\Omega$" in Results; Online Methods, "Theory" (equations (1)–(2) and the variance formula) and "Special Cases".
