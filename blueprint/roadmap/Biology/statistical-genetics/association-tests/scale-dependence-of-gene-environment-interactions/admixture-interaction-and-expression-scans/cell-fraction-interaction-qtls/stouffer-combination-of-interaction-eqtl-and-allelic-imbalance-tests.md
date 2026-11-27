# Stouffer combination of interaction eQTL and allelic-imbalance tests

For a variant, gene and cell type, let $Z_{\mathrm{eQTL}}$ be the signed Wald statistic for the genotype-by-cell-fraction interaction $\beta_f$ in the total-expression regression $y=\mu+\beta x+f+\beta_f\,xf$, and $Z_{\mathrm{AI}}$ the signed statistic for the cell-fraction slope of the allelic fraction in heterozygous carriers, both oriented toward the alternative allele. If $Z_{\mathrm{eQTL}}$ and $Z_{\mathrm{AI}}$ are independent and each standard normal under the null, the combined statistic

$$Z_{\mathrm{DeCAF}}=\frac{Z_{\mathrm{eQTL}}+Z_{\mathrm{AI}}}{\sqrt2}$$

is standard normal under the null. It rewards agreement in sign: effects in opposite directions cancel.

## Depends on

- [Cell-fraction regression of allelic imbalance](cell-fraction-regression-of-allelic-imbalance.md): the allelic-imbalance slope test and the interaction eQTL regression
- [Stouffer's weighted z statistic](../../../../../../Probability/hypothesis-testing/meta-analysis/stouffer-statistic.md): with equal weights

## Proof depends on

- [Stouffer's method](../../../../../../Probability/hypothesis-testing/meta-analysis/has-law-stouffer-statistic.md): the null law

## Expansion

Normality under the null is the variance of a sum of independent unit-variance normals. The source justifies independence by the variation each test uses: the interaction eQTL test uses variation between the genotype classes $0,1,2$, the allelic test variation between the two haplotypes within heterozygotes, as in earlier combined total-and-allelic models. It also reports simulations in which the combined test is calibrated under the null. The equal-weight Stouffer sum coincides with inverse-variance weighting of the two effect estimates only when their standard errors are equal; a sign-agnostic combination such as Fisher's method would lose the consistency check, which the source prefers because allelic and total-expression effects are typically concordant.

## Sources

- C. A. Kalita and A. Gusev, "DeCAF: a novel method to identify cell-type specific regulatory variants and their role in cancer risk", Genome Biology 23 (2022), 152, Methods ("Statistical model to detect cfQTLs"), <https://doi.org/10.1186/s13059-022-02708-9> (PMC9264694).
