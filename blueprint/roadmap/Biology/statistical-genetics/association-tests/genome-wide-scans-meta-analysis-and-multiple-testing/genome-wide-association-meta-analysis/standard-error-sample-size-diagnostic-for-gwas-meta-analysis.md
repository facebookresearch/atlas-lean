# The standard-error versus sample-size diagnostic for GWAS meta-analysis

In a genome-wide association meta-analysis each contributing study $k$ supplies, for every variant $j$, an effect estimate $\hat\beta_{kj}$ from a least-squares regression of a quantitative phenotype $Y$ on the genotype dosage $X_j$ (with an intercept and possibly covariates) and its standard error. **Exact form.** In a fixed-design linear regression with homoscedastic errors of variance $\sigma_{e,j}^2$, the sampling variance of the estimate is

$$\mathrm{SE}_j^2 = \mathrm{var}(\hat\beta_j) = \frac{\sigma_{e,j}^2}{\sum_{i=1}^{N_j} \tilde X_{ij}^2},$$

where $N_j$ is the number of individuals analysed at variant $j$ and $\tilde X_j$ is the genotype vector residualized on the other regressors (the intercept and covariates). The numerator is the error variance of that regression, not the total $\mathrm{var}(Y)$: if $Y = X_j$ exactly, the fitted slope has no sampling error. **Approximation.** Assume each variant explains a negligible share of phenotypic variance, so $\sigma_{e,j}^2 \approx \mathrm{var}(Y)$ (the covariate-adjusted residual variance of the phenotype if the regression has covariates); that the covariates are approximately uncorrelated with genotype, so $\sum_i \tilde X_{ij}^2 \approx N_j\,\mathrm{var}(X_j)$; and that the per-variant sample size is close to the study maximum, $N_j \approx N$. Then $\mathrm{SE}_j^2 \approx \mathrm{var}(Y)/(N\,\mathrm{var}(X_j))$, and taking medians across the $m$ variants of a study,

$$\mathrm{median}_j(\mathrm{SE}_j) \approx \sqrt{\frac{\mathrm{var}(Y)}{N}} \cdot \mathrm{median}_j\Bigl(\frac{1}{\sqrt{\mathrm{var}(X_j)}}\Bigr), \qquad\text{hence}\qquad c\,\sqrt{\mathrm{var}(Y)}\,\frac{1}{\mathrm{median}_j(\mathrm{SE}_j)} \approx \sqrt N, \tag{1}$$

with the study-level constant

$$c = \mathrm{median}_j\Bigl(\frac{1}{\sqrt{\mathrm{var}(X_j)}}\Bigr) \;\approx\; \mathrm{median}_j\Bigl(\frac{1}{\sqrt{2\,\mathrm{MAF}_j(1 - \mathrm{MAF}_j)}}\Bigr), \tag{2}$$

the last approximation assuming Hardy–Weinberg proportions and ignoring imputation uncertainty. Plotting $1/\mathrm{median}_j(\mathrm{SE}_{kj})$ against $\sqrt{N_k}$ across studies therefore gives points approximately on a straight line through the origin with slope $1/(c\sqrt{\mathrm{var}(Y)})$, when the studies share a phenotype transformation, an analysis model and a value of $c$ (which depends on array, imputation panel and ancestry). A study off the line signals a different phenotypic variance or transformation, a misreported sample size, a wrong effect scale, or an inconsistent trait definition.

## Proof sketch

By the Frisch–Waugh–Lovell theorem the coefficient of $X_j$ in the multiple regression equals the slope of the regression of $Y$ on $\tilde X_j$, $\hat\beta_j = \tilde X_j^\top Y / \tilde X_j^\top \tilde X_j$, whose fixed-design variance under homoscedastic errors is $\sigma_{e,j}^2/\tilde X_j^\top\tilde X_j$. Without covariates $\tilde X_j^\top\tilde X_j = N_j\,\widehat{\mathrm{var}}(X_j)$, and $\sigma_{e,j}^2$ is $\mathrm{var}(Y)$ minus the variance explained by the single variant, negligible genome-wide; the remaining approximations are the ones stated. The median is used instead of the mean because the per-variant $\mathrm{var}(X_j)$ varies over orders of magnitude between common and rare variants, and because a few variants have grossly inflated standard errors. Since the median commutes with multiplication by a positive constant, the approximate $\mathrm{SE}_j$ give $\mathrm{median}(\mathrm{SE}_j) \approx \sqrt{\mathrm{var}(Y)/N}\cdot \mathrm{median}(\mathrm{var}(X_j)^{-1/2})$, which is (1). For a diallelic variant in Hardy–Weinberg proportions with minor allele frequency $\mathrm{MAF}$, the genotype dosage has variance $2\,\mathrm{MAF}(1 - \mathrm{MAF})$, which gives (2). Imputed dosages have variance reduced by the imputation quality, so $c$ computed per study from its own frequencies would hide exactly the frequency-distribution differences the diagnostic is meant to reveal; a reference value of $c$ per platform, panel and ancestry is used instead.

## Depends on

- [Hardy–Weinberg proportions](../../../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Sources

- T. W. Winkler, F. R. Day, D. C. Croteau-Chonka et al. (GIANT Consortium), "Quality control and conduct of genome-wide association meta-analyses", Nature Protocols 9 (2014), 1192–1212, "Meta-level QC (Steps 19–26): The SE-N plot (Steps 19–20)", Equations (1)–(2) and Table 3, <https://doi.org/10.1038/nprot.2014.071>, PMCID PMC4083217.
