# Multi-trait conditional analysis from summary data (mtCOJO)

Let $y$ be an outcome, $x_1,\dots,x_t$ covariate traits standardized to variance one, and $z$ a SNP with marginal summary estimates $\hat b_{zy}$ and $\hat{\boldsymbol b}_{zx} = (\hat b_{zx_1},\dots,\hat b_{zx_t})^\top$. Let $\boldsymbol\beta_{xy}$ be the marginal causal effects of the genetic values of the $x_i$ on $y$ (estimated by [GSMR](gsmr-generalized-summary-data-mendelian-randomization.md)), $R_x = (r_g(x_i,x_j))$ the genetic correlation matrix of the covariates and $D = \operatorname{diag}(h^2_{\mathrm{SNP}}(x_i))$ their SNP heritabilities, with $R_x$ invertible.

**Joint effects.** The joint effects of the covariate genetic values on $y$ are obtained from the marginal ones by

$$\boldsymbol b_{xy} = D^{-1/2} R_x^{-1} D^{1/2}\,\boldsymbol\beta_{xy}.$$

**Conditional SNP effect.** The SNP effect on $y$ conditional on the covariate genetic values is

$$\hat b_{zy \mid \boldsymbol b_{xy}} = \hat b_{zy} - \hat{\boldsymbol b}_{zx}^\top \hat{\boldsymbol b}_{xy},$$

with approximate sampling variance

$$\operatorname{var}(\hat b_{zy\mid\boldsymbol b_{xy}}) = \operatorname{var}(\hat b_{zy}) + \hat{\boldsymbol b}_{xy}^\top V_{zx}\hat{\boldsymbol b}_{xy} - 2\hat{\boldsymbol b}_{xy}^\top \operatorname{cov}(\hat b_{zy}, \hat{\boldsymbol b}_{zx}),$$

where $V_{zx} = \operatorname{var}(\hat{\boldsymbol b}_{zx})$ has entries $\rho_{x_ix_j} r_p(x_i,x_j)\sqrt{\operatorname{var}(\hat b_{zx_i})\operatorname{var}(\hat b_{zx_j})}$ and $\operatorname{cov}(\hat b_{zy},\hat b_{zx_i}) = \rho_{x_iy} r_p(x_i,y)\sqrt{\operatorname{var}(\hat b_{zx_i})\operatorname{var}(\hat b_{zy})}$, with $\rho$ the proportion of sample overlap and $r_p$ the phenotypic correlation (the products $\rho r_p$ are approximated by bivariate LD-score-regression intercepts). With no sample overlap the variance is $\operatorname{var}(\hat b_{zy}) + \hat{\boldsymbol b}_{xy}^\top V_{zx}\hat{\boldsymbol b}_{xy}$. The conditional test statistic is $T_{\mathrm{cond}} = \hat b_{zy\mid\boldsymbol b_{xy}}^2/\operatorname{var}(\hat b_{zy\mid\boldsymbol b_{xy}})$.

## Remarks

Fitting $y = x_0 b_0 + \boldsymbol x^\top \boldsymbol b_{xy} + e$ is equivalent to regressing $y$ adjusted for $\boldsymbol x$ on $x_0$ adjusted for $\boldsymbol x$, so a GSMR analysis on conditional SNP effects estimates the effect of $x_0$ given the covariates. The joint-from-marginal transformation is the COJO identity with the LD matrix replaced by the genetic correlation matrix of the covariates and the per-marker scaling by their SNP heritabilities. The variance formula is the variance of a linear combination $\hat b_{zy} - \hat{\boldsymbol b}_{zx}^\top\boldsymbol b_{xy}$ treating $\boldsymbol b_{xy}$ as fixed. Because $\boldsymbol\beta_{xy}$ comes from Mendelian randomization rather than observational regression, the conditional effect avoids the collider bias that arises when conditioning GWAS on a heritable covariate.

## Depends on

- [Generalized summary-data-based Mendelian randomization (GSMR)](gsmr-generalized-summary-data-mendelian-randomization.md)

## Sources

- Z. Zhu, Z. Zheng, F. Zhang et al., "Causal associations between risk factors and common diseases inferred from GWAS summary data", Nature Communications (2018), Methods ("The GSMR method", "Removal of pleiotropic SNPs by HEIDI-outlier", "Multi-trait conditional GWAS analysis using summary data"), <https://doi.org/10.1038/s41467-017-02317-2> (PMC5768719).
