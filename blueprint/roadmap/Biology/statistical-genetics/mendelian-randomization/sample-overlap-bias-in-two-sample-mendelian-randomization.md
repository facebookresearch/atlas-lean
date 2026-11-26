# Sample-overlap bias in two-sample Mendelian randomization

**Setting.** A continuous exposure $X$ and continuous outcome $Y$ are related through linear models, with $K$ mutually uncorrelated genetic instruments and an unmeasured confounder. The instrument–exposure associations are estimated in a sample of size $N_X$ and the instrument–outcome associations in a sample of size $N_Y$; a fraction $s \in [0,1]$ of the participants is shared, where $s$ is measured relative to the **larger** of the two samples. The causal estimate is the two-stage least-squares (2SLS) estimate or, from summarized data, the inverse-variance-weighted (IVW) estimate. Let $\hat\beta_{\mathrm{OLS}}$ be the confounded observational regression coefficient of $Y$ on $X$, and let the **F parameter** $\mathbb{E}(F)$ be the expected first-stage $F$ statistic,

$$F = \frac{N-K-1}{K}\cdot\frac{R^2}{1-R^2},$$

where $R^2$ is the proportion of exposure variance explained by the instruments.

**Statement (approximate bias and size formulas).**

1. *One-sample limit* ($s = 1$). The 2SLS bias is approximately $\sigma_{XY}/(\sigma_X^2\,\mathbb{E}(F))$, where $\sigma_X^2$ is the first-stage error variance and $\sigma_{XY}$ the covariance of the first- and second-stage errors; it points toward the observational association, and the **relative bias** (2SLS bias divided by OLS bias) is approximately $1/\mathbb{E}(F)$.
2. *Disjoint samples* ($s = 0$). Under the causal null the estimate is unbiased; otherwise any weak-instrument bias is toward the null.
3. *Partial overlap, causal null.* The bias is approximately linear in the overlap fraction:

$$\text{bias} \approx \hat\beta_{\mathrm{OLS}} \times s \times \frac{1}{\mathbb{E}(F)}.$$

4. *Type 1 error.* With the approximate variance of the IV estimate

$$\operatorname{Var}(\hat\beta_{\mathrm{IV}}) \approx \frac{\operatorname{Var}(R_Y)}{N\,\operatorname{Var}(X)\,\rho^2},$$

where $N$ is the size of the outcome sample, $R_Y = Y - \hat\beta_X X$ the residual outcome and $\rho^2$ (estimated by $R^2$) the squared instrument–exposure correlation, a nominal two-sided $5\%$ Wald test rejects with probability approximately

$$2 - \Phi\!\left(1.96 - \frac{\text{bias}}{\text{se}}\right) - \Phi\!\left(1.96 + \frac{\text{bias}}{\text{se}}\right).$$

For example, with $\mathbb{E}(F) = 10$ the relative bias is $10\%$ with full overlap, $5\%$ with $50\%$ overlap and $3\%$ with $30\%$ overlap. In a case–control outcome sample, estimating the instrument–exposure associations in **controls only** removed the bias in simulation even with complete overlap.

## Depends on

- [Inverse-variance-weighted estimator](ivw.md)

## Expansion

In one sample, the first-stage fitted values over-fit chance correlations of the instruments with the confounder, so the fitted exposure and the outcome stay correlated through the confounder even when the causal effect is zero. With disjoint samples, the fitted exposure in the outcome sample is an externally weighted allele score with non-differential estimation error, which attenuates toward the null, as regression dilution does. When the samples partly overlap, the dependence between the first-stage and second-stage error vectors comes only from the shared participants: covariance is bilinear, so the covariance, and hence the first-order bias, scales with the fraction of shared individuals, diluted by participants present in only one sample. For a single SNP, $R^2 \approx 2\hat\alpha^2\,\mathrm{MAF}(1-\mathrm{MAF})$ with $\hat\alpha$ in exposure standard-deviation units; taking $R^2$ from an external sample avoids plugging in the noisy observed $F$ statistic.

## Sources

- S. Burgess, N. M. Davies and S. G. Thompson, "Bias due to participant overlap in two-sample Mendelian randomization", Genetic Epidemiology (2016), Section 2, Equations (1) and (3)–(6), and Sections 3–4, <https://doi.org/10.1002/gepi.21998> (PMC5082560).
