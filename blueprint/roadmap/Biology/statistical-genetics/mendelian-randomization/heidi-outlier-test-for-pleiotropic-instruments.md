# HEIDI-outlier test for pleiotropic instruments

In the setting of [GSMR](gsmr-generalized-summary-data-mendelian-randomization.md), let $\hat b_{xy(i)}$ be the ratio estimates at $m$ instruments with delta-method covariances $\operatorname{cov}(\hat b_{xy(i)}, \hat b_{xy(j)})$ (which account for the LD correlation $r_{ij}$ and for sampling error in both $\hat b_{zx}$ and $\hat b_{zy}$). Choose a target instrument "top" that is strongly associated with the exposure but is not an extreme value of $\hat b_{xy}$ (the paper takes the most exposure-associated SNP within the third quintile of the distribution of $\hat b_{xy}$).

**Statistic.** For each instrument $i \ne \text{top}$ define

$$\hat d_i = \hat b_{xy(i)} - \hat b_{xy(\text{top})}, \qquad \operatorname{var}(\hat d_i) = \operatorname{var}(\hat b_{xy(i)}) + \operatorname{var}(\hat b_{xy(\text{top})}) - 2\operatorname{cov}(\hat b_{xy(i)}, \hat b_{xy(\text{top})}),$$

and $T_i = \hat d_i^2/\operatorname{var}(\hat d_i)$. Under a causal model with no pleiotropy, $E[\hat b_{xy(i)}] = b_{xy}$ for every valid instrument, so $E[\hat d_i] = 0$ and $T_i$ is approximately $\chi^2_1$. Instruments with $P(\chi^2_1 > T_i) < 0.01$ are removed as pleiotropic outliers before the GSMR estimate is computed.

## Remarks

A pleiotropic SNP $i$ has $\hat b_{zy(i)} = b_{xy}\hat b_{zx(i)} + \delta_i + \text{noise}$, so its ratio estimate is shifted by $\delta_i / b_{zx(i)}$ and $\hat d_i$ acquires a non-zero mean. The power of each test grows with the exposure association of the reference SNP, which argues for a strong target; taking the single strongest SNP is fragile because extreme exposure effects are themselves often pleiotropic. The lenient threshold $0.01$ is deliberate: discarding a valid instrument costs only power, not calibration of the subsequent GSMR test, and with no outliers about $1\%$ of instruments are removed by chance.

## Depends on

- [Generalized summary-data-based Mendelian randomization (GSMR)](gsmr-generalized-summary-data-mendelian-randomization.md)

## Sources

- Z. Zhu, Z. Zheng, F. Zhang et al., "Causal associations between risk factors and common diseases inferred from GWAS summary data", Nature Communications (2018), Methods ("The GSMR method", "Removal of pleiotropic SNPs by HEIDI-outlier", "Multi-trait conditional GWAS analysis using summary data"), <https://doi.org/10.1038/s41467-017-02317-2> (PMC5768719).
