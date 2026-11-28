# Generalized summary-data-based Mendelian randomization (GSMR)

Let $z_1,\dots,z_m$ be SNPs associated with an exposure $x$ (near-independent after clumping, with residual LD correlations $r_{ij}$ known from a reference panel). For each SNP let $\hat b_{zx(i)}$ and $\hat b_{zy(i)}$ be its marginal effect estimates on the exposure and on the outcome $y$, from independent samples, with sampling variances $\operatorname{var}(\hat b_{zx(i)})$ and $\operatorname{var}(\hat b_{zy(i)})$. The single-SNP ratio estimate is $\hat b_{xy(i)} = \hat b_{zy(i)} / \hat b_{zx(i)}$.

**Model.** If $x$ has a causal effect $b_{xy}$ on $y$ and no instrument is pleiotropic, every ratio estimate has the same expectation, and approximately

$$\hat{\boldsymbol b}_{xy} = (\hat b_{xy(1)},\dots,\hat b_{xy(m)})^\top \sim N(\mathbf 1\, b_{xy},\, V),$$

where, by the delta method, the diagonal and off-diagonal entries of $V$ are

$$V_{ii} = b_{xy(i)}^2\left(\frac{\operatorname{var}(\hat b_{zx(i)})}{b_{zx(i)}^2} + \frac{\operatorname{var}(\hat b_{zy(i)})}{b_{zy(i)}^2} - \frac{\operatorname{var}(\hat b_{zx(i)})^2}{b_{zx(i)}^4}\right),$$

$$V_{ij} = \frac{r_{ij}\sqrt{\operatorname{var}(\hat b_{zy(i)})\operatorname{var}(\hat b_{zy(j)})}}{b_{zx(i)}b_{zx(j)}} + b_{xy(i)}b_{xy(j)}\left(\frac{r_{ij}\sqrt{\operatorname{var}(\hat b_{zx(i)})\operatorname{var}(\hat b_{zx(j)})}}{b_{zx(i)}b_{zx(j)}} - \frac{\operatorname{var}(\hat b_{zx(i)})\operatorname{var}(\hat b_{zx(j)})}{b_{zx(i)}^2 b_{zx(j)}^2}\right) \quad (i \ne j).$$

**Estimator.** With $V$ evaluated at the estimates and assumed invertible, the GSMR estimate is the generalized least-squares estimate of the common mean,

$$\hat b_{xy} = (\mathbf 1^\top V^{-1}\mathbf 1)^{-1}\,\mathbf 1^\top V^{-1}\hat{\boldsymbol b}_{xy}, \qquad \operatorname{var}(\hat b_{xy}) = (\mathbf 1^\top V^{-1}\mathbf 1)^{-1},$$

and causality is tested with $T_{\mathrm{GSMR}} = \hat b_{xy}^2/\operatorname{var}(\hat b_{xy})$, which is $\chi^2_1$ under $b_{xy} = 0$.

## Remarks

Under $\hat{\boldsymbol b}_{xy} \sim N(\mathbf 1 b_{xy}, V)$ the log-likelihood in $b_{xy}$ is $-\tfrac12(\hat{\boldsymbol b}_{xy} - \mathbf 1 b_{xy})^\top V^{-1}(\hat{\boldsymbol b}_{xy} - \mathbf 1 b_{xy})$; setting its derivative to zero gives the displayed estimator, and its variance is the inverse Fisher information $(\mathbf 1^\top V^{-1}\mathbf 1)^{-1}$. When $V$ is diagonal and the exposure-side variance terms are dropped, $V_{ii} = \operatorname{var}(\hat b_{zy(i)})/b_{zx(i)}^2$ and $\hat b_{xy}$ reduces to the inverse-variance-weighted estimate. Because log odds ratios are free of ascertainment bias, the method applies to case–control outcomes and the estimate refers to the general population.

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)

## Sources

- Z. Zhu, Z. Zheng, F. Zhang et al., "Causal associations between risk factors and common diseases inferred from GWAS summary data", Nature Communications (2018), Methods ("The GSMR method", "Removal of pleiotropic SNPs by HEIDI-outlier", "Multi-trait conditional GWAS analysis using summary data"), <https://doi.org/10.1038/s41467-017-02317-2> (PMC5768719).
