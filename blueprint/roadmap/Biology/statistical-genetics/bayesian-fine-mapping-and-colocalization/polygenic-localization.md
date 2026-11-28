# Polygenic localization

Let $\beta_1,\dots,\beta_m$ be the standardized causal effects of $m$ common SNPs, not all zero, and fix $p \in (0,1]$.

**Oracle localization size.** Let $s_1,\dots,s_m$ order the SNPs so that $\beta_{s_1}^2 \ge \beta_{s_2}^2 \ge \dots \ge \beta_{s_m}^2$. Define

$$M_p^* = \min\Bigl\{k : \sum_{j=1}^{k}\beta_{s_j}^2 \Big/ \sum_{i=1}^{m}\beta_i^2 \ge p\Bigr\},$$

the size of the smallest set of SNPs causally explaining a fraction $p$ of the common-SNP heritability.

**Localization under an estimated ranking.** For any ranking $s'_1,\dots,s'_m$ of the SNPs define $M_p$ in the same way with $s'$ in place of $s$. Then $M_p \ge M_p^*$ for every ranking, with equality for the oracle ranking.

**Estimator (PolyLoc).** Rank SNPs by posterior mean squared effect from functionally informed fine-mapping, group them into bins of similar posterior per-SNP heritability, re-estimate the average $\operatorname{var}[\beta_i]$ in each bin by stratified LD-score regression on an independent sample (treating effects as mean zero within a bin), and report the smallest $k$ with $\sum_{j \le k}\operatorname{var}[\beta_{\hat s_j}] / \sum_i \operatorname{var}[\beta_i] \ge p$. This estimates $M_p$ and is therefore a conservative (upper) estimate of $M_p^*$.

## Depends on

- [Functionally informed prior causal probabilities (PolyFun)](functionally-informed-prior-causal-probabilities-polyfun.md)
- [Heritability of a marker category](../stratified-ld-score-regression/cat-h2.md)

## Expansion

For each $k$, the sum of the $k$ largest $\beta_i^2$ is at least the sum of $\beta^2$ over any $k$ SNPs, so the cumulative fraction under the oracle ordering dominates that under any other ordering and reaches $p$ no later. Using a separate sample for the bin heritabilities avoids the winner's curse that would arise from reusing the fine-mapping data. Across 49 UK Biobank traits $M_{50\%}$ ranged from about 28 SNPs (hair color) to about 3,400 (height) to about 2 million (number of children); its gap from $M_p^*$ shrinks as fine-mapping power grows.

## Sources

- O. Weissbrod, F. Hormozdiari, C. Benner et al., "Functionally informed fine-mapping and polygenic localization of complex trait heritability", Nature Genetics (2020), Results ("Polygenic localization of 49 complex traits") and Online Methods ("Polygenic localization"), <https://doi.org/10.1038/s41588-020-00735-5>.
