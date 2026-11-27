# Deviation regression model for variance QTLs

**Definition.** For a SNP with minor-allele count $i \in \{0,1,2\}$ and phenotypes $Y_{ij}$ of individuals $j$ with genotype $i$, let $\tilde Y_i$ be the median phenotype within genotype group $i$ and

$$Z_{ij} = \big|Y_{ij} - \tilde Y_i\big| .$$

The **deviation regression model** (DRM) fits the linear regression $Z_{ij} = \eta_0 + \eta_1 i + e_{ij}$ (allowing imputed dosages as the regressor) and tests $\eta_1 = 0$; a significant slope marks a **variance QTL** (vQTL). The Brown–Forsythe test uses the same $Z_{ij}$ in a one-way ANOVA on genotype groups, and Levene's test uses group means instead of medians.

**Proposition (interactions create vQTLs).** Let $Y = \mu + \gamma X_1X_2 + \varepsilon$, where $X_1$ is a genotype, $X_2$ a second locus or environmental exposure independent of $X_1$ with mean $m$ and variance $\sigma_2^2$, and $\varepsilon$ independent noise with variance $\sigma^2$. Then

$$\mathbb E[Y \mid X_1 = x] = \mu + \gamma m x,\qquad \operatorname{Var}(Y \mid X_1 = x) = \gamma^2\sigma_2^2\,x^2 + \sigma^2 .$$

So an interaction with $\gamma \ne 0$ makes $X_1$ a vQTL even when it has no marginal mean effect ($m = 0$), and a variance test can nominate interacting SNPs without specifying the partner $X_2$, which removes the multiple-testing burden of an exhaustive interaction search.

In simulations the DRM kept nominal false-positive rates under strong mean effects and non-normal (chi-square) noise, where tests based on squared residuals did not, and applying it to body mass index in a large biobank followed by targeted interaction tests found gene–environment interactions at loci such as FTO.

## Expansion

Conditioning on $X_1 = x$ leaves $\gamma xX_2 + \varepsilon$ as the random part, whose mean is $\gamma xm$ and whose variance is $\gamma^2x^2\sigma_2^2 + \sigma^2$ by independence; this gives both displays. For a symmetric error law, the expected absolute deviation from the median is proportional to the standard deviation within each genotype class, so a slope in $Z$ against allele count detects a genotype-dependent scale. Centring at within-genotype medians rather than means makes the deviations insensitive to mean effects and robust to skew, which is the source of the calibration advantage over mean-centred or squared-residual approaches. Phenotype transformations (log, reciprocal, rank inverse normal) change both mean and variance effects, so a vQTL found on one scale need not persist on another.

## Sources

- A. R. Marderstein, E. R. Davenport, S. Kulm et al., "Leveraging phenotypic variability to identify genetic interactions in human phenotypes", American Journal of Human Genetics (2021), Material and Methods ("Description and implementation of variance tests") and Results, Figures 1–2, <https://doi.org/10.1016/j.ajhg.2020.11.016> (PMC7820920).
