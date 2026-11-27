# LT-FH association statistic

Let $g_1, \dots, g_N$ be genotypes at a test SNP and $\hat\epsilon_1, \dots, \hat\epsilon_N$ the [posterior mean genetic liabilities](posterior-mean-genetic-liability.md) of the $N$ genotyped individuals. The LT-FH statistic is

$$T_{\mathrm{LT\text{-}FH}} = N\, r^2(g, \hat\epsilon),$$

where $r^2$ is the squared sample correlation, compared with a $\chi^2_1$ distribution. Treating $\hat\epsilon$ as a continuous phenotype, this generalizes the Armitage trend test (which is $N r^2(g, z)$ for the case indicator $z$) and is equivalent to the score test for regression of $\hat\epsilon$ on $g$. Covariates such as principal components can be included, or the mixed-model method BOLT-LMM can be applied to $\hat\epsilon$.

**Reduction to case-control GWAS.** If no family history is observed, $\hat\epsilon_i = a + b z_i$ with $b = h^2\varphi(T)\big(\tfrac1K + \tfrac1{1-K}\big) > 0$, and since $r^2$ is invariant under affine maps with nonzero slope, $T_{\mathrm{LT\text{-}FH}} = N r^2(g, z)$ equals the Armitage trend statistic.

## Depends on

- [Posterior mean genetic liability given case-control status and family history](posterior-mean-genetic-liability.md)
- [The Cochran–Armitage statistic is N r²](../../../cochran-armitage-trend-test/ca-stat-eq-mul-sample-corr-sq.md)

## Expansion

The sample correlation is unchanged when either variable is shifted or rescaled by a positive (or, for $r^2$, any nonzero) factor; the closed form for $E[\epsilon_g \mid z]$ makes the posterior mean affine in $z$, which gives the reduction. With family history, $\hat\epsilon$ separates configurations that $z$ merges (controls with and without affected parents), which increased power in simulations by $55\%$ over the proxy-case method GWAX and more over GWAS at prevalence $5\%$ and $h^2 = 50\%$, while null calibration was unchanged (mean null $\chi^2 = 1.00$ for all methods). Because no genotype data enter $\hat\epsilon$, linkage disequilibrium between SNPs does not affect calibration. Raw LT-FH effect sizes are not on the liability scale but can be converted to the observed scale through the effective sample size.

## Sources

- M. L. A. Hujoel, S. Gazal, P.-R. Loh, N. Patterson and A. L. Price, "Liability threshold modeling of case-control status and family history of disease increases association power", Nature Genetics 52 (2020), 541–547, Results ("Overview of methods", "Simulations") and Methods ("LT-FH association statistic"), <https://doi.org/10.1038/s41588-020-0613-6>, PMCID: PMC7210076.
