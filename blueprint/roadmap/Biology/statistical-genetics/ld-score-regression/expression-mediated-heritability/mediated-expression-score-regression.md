# Mediated expression score regression (MESC)

In the model of [expression-mediated heritability](expression-mediated-heritability.md), the total effect of SNP $k$ on the trait is

$$\omega_k = \sum_{i=1}^{G}\beta_{ik}\alpha_i + \gamma_k.$$

**Regression identity.** Write $\beta_{\cdot k} = (\beta_{1k},\dots,\beta_{Gk})$ and assume, conditionally on $\beta_{\cdot k}$, zero cross moments and constant second moments:

$$\mathbb E[\alpha_i\alpha_{i'} \mid \beta_{\cdot k}] = 0 \ (i \ne i'), \quad \mathbb E[\alpha_i\gamma_k \mid \beta_{\cdot k}] = 0, \quad \mathbb E[\alpha_i^2 \mid \beta_{\cdot k}] = \mathbb E[\alpha^2], \quad \mathbb E[\gamma_k^2 \mid \beta_{\cdot k}] = \mathbb E[\gamma^2].$$

The last two are conditional forms of gene–eQTL and pleiotropy–eQTL independence; zero covariance of squared effects ($\operatorname{Cov}(\alpha^2,\beta^2) = 0$, $\operatorname{Cov}(\gamma^2,\beta^2) = 0$) does not imply them, and none of these implies the cross-moment conditions (the one-SNP, two-gene example with $\alpha_1 = \alpha_2 = U$ on [the heritability page](expression-mediated-heritability.md) has $\mathbb E[\omega^2 \mid \beta] = 4\operatorname{Var}(U)$ against $2\operatorname{Var}(U)$ from the identity). Then

$$\mathbb E\!\left[\omega_k^2 \,\middle|\, \beta_{\cdot k}\right] = \mathbb E[\alpha^2]\sum_{i=1}^{G}\beta_{ik}^2 + \mathbb E[\gamma^2].$$

Regressing $\omega_k^2$ on the expression score $\sum_i\beta_{ik}^2$ across SNPs gives slope $\mathbb E[\alpha^2]$ and intercept $\mathbb E[\gamma^2]$, so

$$\hat h^2_{\mathrm{med}} = G\,\widehat{\mathbb E[\alpha^2]}\,\widehat{\mathbb E[h^2_{\mathrm{cis}}]}, \qquad \hat h^2_{\mathrm{nonmed}} = M\,\widehat{\mathbb E[\gamma^2]}.$$

With GWAS and eQTL summary statistics the same regression is run on association statistics with an LD-score covariate to absorb LD (stratified MESC is a special case of stratified LD-score regression with expression scores per gene category). Violating either independence condition biases $\hat h^2_{\mathrm{med}}$ in the direction of the correlation between eQTL magnitude and gene or non-mediated effect magnitude.

## Proof sketch

Squaring $\omega_k$ gives $\sum_{i,i'}\beta_{ik}\beta_{i'k}\alpha_i\alpha_{i'} + 2\sum_i\beta_{ik}\alpha_i\gamma_k + \gamma_k^2$. Taking the expectation given $\beta_{\cdot k}$, the conditional zero cross moments remove the terms $i \ne i'$ and the $\alpha\gamma$ terms, leaving $\sum_i\beta_{ik}^2\,\mathbb E[\alpha_i^2 \mid \beta_{\cdot k}] + \mathbb E[\gamma_k^2\mid\beta_{\cdot k}]$, and the constant conditional second moments turn these into $\mathbb E[\alpha^2]$ and $\mathbb E[\gamma^2]$. For stratified MESC the same holds with $\mathbb E[\alpha_i^2 \mid \beta_{\cdot k}]$ constant within each gene category, giving one slope per category. The identity is an LD-score-type regression in which the "LD score" is the total squared cis-eQTL effect of a SNP. Using eQTLs from assayed rather than causal tissues makes the slope estimate $h^2_{\mathrm{med;assayed}}$.

## Depends on

- [Expression-mediated heritability](expression-mediated-heritability.md)
- [Stratified LD-score regression](../../stratified-ld-score-regression/integral-chi-sq-of-annot.md)

## Sources

- D. W. Yao, L. J. O'Connor, A. L. Price et al., "Quantifying genetic effects on disease mediated by assayed gene expression levels", Nature Genetics (2020), Methods ("Definition of $h^2_{\mathrm{med}}$", "Unstratified MESC" with Equations 1–2, "Model assumptions", "Stratified MESC"), <https://doi.org/10.1038/s41588-020-0625-2> (PMC7276299).
