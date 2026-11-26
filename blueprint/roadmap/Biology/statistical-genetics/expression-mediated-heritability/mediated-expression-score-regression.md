# Mediated expression score regression (MESC)

In the model of [expression-mediated heritability](expression-mediated-heritability.md), the total effect of SNP $k$ on the trait is
$$\omega_k = \sum_{i=1}^{G}\beta_{ik}\alpha_i + \gamma_k.$$

**Regression identity.** Assume $\alpha$ and $\gamma$ are conditionally independent given the eQTL effects, and the two effect-size independence conditions hold: gene–eQTL independence ($\operatorname{Cov}(\alpha^2, \beta^2) = 0$ across genes) and pleiotropy–eQTL independence ($\operatorname{Cov}(\gamma^2,\beta^2) = 0$ across SNPs). Then
$$\mathbb E\!\left[\omega_k^2 \,\middle|\, \beta_{1k},\dots,\beta_{Gk}\right] = \mathbb E[\alpha^2]\sum_{i=1}^{G}\beta_{ik}^2 + \mathbb E[\gamma^2].$$
Regressing $\omega_k^2$ on the expression score $\sum_i\beta_{ik}^2$ across SNPs gives slope $\mathbb E[\alpha^2]$ and intercept $\mathbb E[\gamma^2]$, so
$$\hat h^2_{\mathrm{med}} = G\,\widehat{\mathbb E[\alpha^2]}\,\widehat{\mathbb E[h^2_{\mathrm{cis}}]}, \qquad \hat h^2_{\mathrm{nonmed}} = M\,\widehat{\mathbb E[\gamma^2]}.$$
With GWAS and eQTL summary statistics the same regression is run on association statistics with an LD-score covariate to absorb LD (stratified MESC is a special case of stratified LD-score regression with expression scores per gene category). Violating either independence condition biases $\hat h^2_{\mathrm{med}}$ in the direction of the correlation between eQTL magnitude and gene or non-mediated effect magnitude.

## Depends on

- [Expression-mediated heritability](expression-mediated-heritability.md)
- [Stratified LD-score regression](../stratified-ld-score-regression/integral-chi-sq-of-annot.md)

## Expansion

Squaring $\omega_k$ and taking expectations given the eQTL effects, the cross terms $\beta_{ik}\beta_{i'k}\mathbb E[\alpha_i\alpha_{i'}]$ and $\beta_{ik}\mathbb E[\alpha_i\gamma_k]$ vanish for independent mean-zero effects, leaving $\sum_i\beta_{ik}^2\mathbb E[\alpha_i^2 \mid \beta] + \mathbb E[\gamma_k^2\mid\beta]$; the independence conditions remove the conditioning, giving constants $\mathbb E[\alpha^2]$ and $\mathbb E[\gamma^2]$. The identity is an LD-score-type regression in which the "LD score" is the total squared cis-eQTL effect of a SNP. Using eQTLs from assayed rather than causal tissues makes the slope estimate $h^2_{\mathrm{med;assayed}}$.

## Sources

- D. W. Yao, L. J. O'Connor, A. L. Price et al., "Quantifying genetic effects on disease mediated by assayed gene expression levels", Nature Genetics (2020), Methods ("Definition of $h^2_{\mathrm{med}}$", "Unstratified MESC" with Equations 1–2, "Model assumptions", "Stratified MESC"), <https://doi.org/10.1038/s41588-020-0625-2> (PMC7276299).
