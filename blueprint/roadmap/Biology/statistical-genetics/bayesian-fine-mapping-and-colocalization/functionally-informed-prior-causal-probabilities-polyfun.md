# Functionally informed prior causal probabilities (PolyFun)

**Model.** Standardized phenotypes follow $y = \sum_i x_i\beta_i + \epsilon$ with standardized genotypes $x_i$. Each SNP $i$ has a vector of functional annotations $a_i$, and its effect has the point-normal prior

$$\beta_i \mid a_i \sim \begin{cases} N\bigl(0, \operatorname{var}[\beta_i \mid \beta_i \ne 0]\bigr) & \text{with probability } P(\beta_i \ne 0 \mid a_i),\\ 0 & \text{otherwise,}\end{cases}$$

where the causal variance $\operatorname{var}[\beta_i \mid \beta_i \ne 0] = \sigma^2_c$ does not depend on $a_i$. Call $\operatorname{var}[\beta_i \mid a_i]$ the per-SNP heritability; when effects have mean zero and are uncorrelated, the total SNP heritability is $\sum_i \operatorname{var}[\beta_i \mid a_i]$.

**Proposition.** Under this model

$$P(\beta_i \ne 0 \mid a_i) = \frac{\operatorname{var}[\beta_i \mid a_i]}{\sigma^2_c},$$

so prior causal probabilities are proportional to per-SNP heritabilities. In a locus, normalizing the priors to sum to one removes the unknown constant $\sigma^2_c$ (one causal SNP expected a priori); methods such as SuSiE are invariant to this scaling.

**Estimation.** Per-SNP heritabilities are estimated with the stratified LD-score model $\operatorname{var}[\beta_i \mid a_i] = \sum_c \tau_c a_{ic}$, fitting $\tau$ by minimizing $\sum_i(\chi^2_i - n\sum_c \tau_c\ell(i,c) - nb - 1)^2$ with an $L_2$ penalty, where $\ell(i,c) = \sum_j r_{ij}^2 a_{jc}$. To be robust to misspecification, SNPs are then grouped into bins of similar estimated per-SNP heritability and each SNP is assigned its bin's re-estimated heritability divided by the bin size, a piecewise-constant approximation of $\operatorname{var}[\beta_i \mid a_i]$. Enrichments are estimated on the odd (even) chromosomes and applied to the even (odd) ones, and bin heritabilities exclude the target chromosome, to avoid winner's curse.

## Depends on

- [Stratified LD-score regression](../stratified-ld-score-regression/integral-chi-sq-of-annot.md)
- [Posterior inclusion probability](pip.md)

## Expansion

Let $c_i = \mathbf 1[\beta_i \ne 0]$. By the law of total variance, $\operatorname{var}[\beta_i \mid a_i] = \mathbb E[\operatorname{var}(\beta_i \mid a_i, c_i)] + \operatorname{var}(\mathbb E[\beta_i \mid a_i, c_i])$; the second term vanishes because the conditional mean is $0$ in both cases, and the first equals $P(c_i = 1 \mid a_i)\,\sigma^2_c$. Using genome-wide data rather than only significant loci lets many annotations be weighted, and in 49 UK Biobank traits functionally informed priors with SuSiE gave over 32% more variants with posterior inclusion probability above $0.95$ than SuSiE with uniform priors.

## Sources

- O. Weissbrod, F. Hormozdiari, C. Benner et al., "Functionally informed fine-mapping and polygenic localization of complex trait heritability", Nature Genetics (2020), Results Eq. (1) and Online Methods ("PolyFun fine-mapping method", Eq. (2)), <https://doi.org/10.1038/s41588-020-00735-5>.
