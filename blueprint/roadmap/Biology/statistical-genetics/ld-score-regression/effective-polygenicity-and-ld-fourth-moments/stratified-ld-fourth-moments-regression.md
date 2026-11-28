# Stratified LD fourth moments regression

Let GWAS marginal effect estimates $\hat\alpha_j$ (in per-normalized-genotype units) be available for $M$ reference SNPs, with LD $r_{jk}$ from a reference panel. Define, for SNP $j$ and an annotation category $C$,

$$\ell^{(2)}_{j,C} = \sum_{k \in C} r_{jk}^2 \quad \text{(LD score)}, \qquad \ell^{(4)}_{j,C} = \sum_{k \in C} r_{jk}^4 \quad \text{(LD fourth moment)}.$$

Stratified LD fourth moments regression (S-LD4M) fits, across SNPs,

$$\mathbb E\big(\alpha_j^4 \mid \ell^{(2)}_j, \ell^{(4)}_j\big) \approx 3\big(\ell^{(2)}_j \cdot \tau\big)^2 + \ell^{(4)}_j \cdot K,$$

where $\tau$ is the vector of stratified LD score regression coefficients (per-SNP heritabilities by category) and $K$ is the vector of fourth-moment coefficients. The first term is the fourth moment that a Gaussian (infinitesimal) architecture with the same second moments would give; $K$ measures excess kurtosis of the causal effect-size distribution. For a single category,

$$K = 3\,\mathbb E(\beta^2)\big[\mathbb E_{h^2}(\alpha^2) - \mathbb E(\alpha^2)\big] = \frac{3 h^2}{M}\left[\frac{h^2}{M_e} - \frac{h^2}{M_{\mathrm{indep}}}\right],$$

where $h^2$ is the heritability tagged by the reference SNPs, $M_{\mathrm{indep}}$ is the effective number of independent SNPs and $M_e$ is the [effective number of independently associated SNPs](effective-number-of-independently-associated-snps.md). Hence, with $h^2$ estimated by stratified LD score regression,

$$M_e = \left(\frac{K M}{3 h^4} + \frac{1}{M_{\mathrm{indep}}}\right)^{-1},$$

and $K = 0$ exactly when $M_e = M_{\mathrm{indep}}$, as under an infinitesimal architecture.

## Remarks

The regression is the fourth-moment analogue of LD score regression: squared $\chi^2$ statistics (fourth powers of signed $z$ scores) play the role that $\chi^2$ statistics play there. If $\alpha_j = \sum_k r_{jk} \beta_k$ with independent causal effects, then $\mathbb E\alpha_j^4 = 3\big(\sum_k r_{jk}^2 \mathbb E\beta_k^2\big)^2 + \sum_k r_{jk}^4 \big(\mathbb E\beta_k^4 - 3 (\mathbb E\beta_k^2)^2\big)$, which has exactly the two-term form above with per-category second moments in $\tau$ and per-category excess fourth moments in $K$ (Appendix A of the paper gives the full derivation, including the treatment of sampling noise in $\hat\alpha_j$). Standard errors come from a block jackknife over contiguous SNP blocks, the run time is linear in the number of regression SNPs, and only well-powered trait–annotation pairs (heritability $z > 2$, $M_e$ $z > 1/2$) are reported because the estimator is a ratio with a noisy denominator, so medians rather than means are approximately unbiased in simulations.

## Depends on

- [Effective number of independently associated SNPs](effective-number-of-independently-associated-snps.md)
- [Stratified LD-score regression](../../stratified-ld-score-regression/integral-chi-sq-of-annot.md)

## Sources

- L. J. O'Connor, A. P. Schoech, F. Hormozdiari, S. Gazal, N. Patterson and A. L. Price, "Extreme polygenicity of complex traits is explained by negative selection", The American Journal of Human Genetics 105 (2019), 456–476, Material and Methods ("Estimating Polygenicity: Stratified LD Fourth Moments Regression", Equations 2–3) and Appendix A, <https://doi.org/10.1016/j.ajhg.2019.07.003> (PMC6732528).
