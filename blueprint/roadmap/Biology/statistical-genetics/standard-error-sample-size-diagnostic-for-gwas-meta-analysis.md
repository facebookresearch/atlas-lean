# The standard-error versus sample-size diagnostic for GWAS meta-analysis

In a genome-wide association meta-analysis each contributing study $k$ supplies, for every variant $j$, an effect estimate $\hat\beta_{kj}$ from a linear regression of a quantitative phenotype $Y$ on the genotype dosage $X_j$ and its standard error. For a study of size $N$ the sampling variance of the estimate is

$$\mathrm{SE}_j^2 = \mathrm{var}(\hat\beta_j) = \frac{\mathrm{var}(Y)}{N \cdot \mathrm{var}(X_j)},$$

where $\mathrm{var}(Y)$ is the residual variance of the phenotype if the regression is covariate-adjusted. Taking medians across the $m$ variants of a study, and assuming the per-variant sample size is close to the study maximum $N$,

$$\mathrm{median}_j(\mathrm{SE}_j) = \sqrt{\frac{\mathrm{var}(Y)}{N}} \cdot \mathrm{median}_j\Bigl(\frac{1}{\sqrt{\mathrm{var}(X_j)}}\Bigr), \qquad\text{hence}\qquad c\,\sqrt{\mathrm{var}(Y)}\,\frac{1}{\mathrm{median}_j(\mathrm{SE}_j)} = \sqrt N, \tag{1}$$

with the study-level constant

$$c = \mathrm{median}_j\Bigl(\frac{1}{\sqrt{\mathrm{var}(X_j)}}\Bigr) \;\approx\; \mathrm{median}_j\Bigl(\frac{1}{\sqrt{2\,\mathrm{MAF}_j(1 - \mathrm{MAF}_j)}}\Bigr), \tag{2}$$

the approximation ignoring imputation uncertainty. Plotting $1/\mathrm{median}_j(\mathrm{SE}_{kj})$ against $\sqrt{N_k}$ across studies therefore gives points on a straight line through the origin with slope $1/(c\sqrt{\mathrm{var}(Y)})$, when the studies share a phenotype transformation, an analysis model and a value of $c$ (which depends on array, imputation panel and ancestry). A study off the line signals a different phenotypic variance or transformation, a misreported sample size, a wrong effect scale, or an inconsistent trait definition.

## Depends on

- [Hardy–Weinberg equilibrium](../population-genetics/hardy-weinberg-law/offspring-offspring.md)

## Expansion

In the simple regression of $Y$ on $X_j$, $\hat\beta_j = \widehat{\mathrm{cov}}(X_j, Y)/\widehat{\mathrm{var}}(X_j)$ has variance $\sigma^2/(N\,\mathrm{var}(X_j))$ with $\sigma^2$ the residual variance, which is $\mathrm{var}(Y)$ up to the variance explained by the single variant, negligible genome-wide. The median is used instead of the mean because the per-variant $\mathrm{var}(X_j)$ varies over orders of magnitude between common and rare variants, and because a few variants have grossly inflated standard errors. Since the median is equivariant under monotone transformations, $\mathrm{median}(\mathrm{SE}_j) = \sqrt{\mathrm{var}(Y)/N}\cdot \mathrm{median}(\mathrm{var}(X_j)^{-1/2})$, which is (1). For a diallelic variant in Hardy–Weinberg proportions with minor allele frequency $\mathrm{MAF}$, the genotype dosage has variance $2\,\mathrm{MAF}(1 - \mathrm{MAF})$, which gives (2). Imputed dosages have variance reduced by the imputation quality, so $c$ computed per study from its own frequencies would hide exactly the frequency-distribution differences the diagnostic is meant to reveal; a reference value of $c$ per platform, panel and ancestry is used instead.

## Sources

- T. W. Winkler, F. R. Day, D. C. Croteau-Chonka et al. (GIANT Consortium), "Quality control and conduct of genome-wide association meta-analyses", Nature Protocols 9 (2014), 1192–1212, "Meta-level QC (Steps 19–26): The SE-N plot (Steps 19–20)", Equations (1)–(2) and Table 3, <https://doi.org/10.1038/nprot.2014.071>, PMCID PMC4083217.
