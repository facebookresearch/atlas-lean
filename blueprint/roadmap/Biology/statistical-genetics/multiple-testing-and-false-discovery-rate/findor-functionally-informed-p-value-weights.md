# FINDOR: p-value weights from stratified LD-score predictions

Let SNP $j$ have GWAS association statistic $\chi^2_j$ from $N_j$ samples, and let annotations $C$ have LD scores $\ell(j,C) = \sum_k C(k)\,r_{kj}^2$. Stratified LD-score regression posits
$$E[\chi^2_j] = N_j\sum_C \tau_C\,\ell(j,C) + N_j\alpha + 1,$$
with $\tau_C$ the per-SNP heritability effect of annotation $C$ and $\alpha$ a confounding term.

**Weights.** (1) Fit $\hat\tau_C, \hat\alpha$ and predict the tagged variance of every SNP, $\widehat{\chi^2_j} = N_j\sum_C\hat\tau_C\ell(j,C) + N_j\hat\alpha + 1$. (2) Sort SNPs by $\widehat{\chi^2_j}$ into $B$ equal-size bins (the paper uses $B = 100$) and, in each bin $b$, estimate the null and non-null proportions $\hat\pi_{0,b}$, $\hat\pi_{1,b}$ from the p-value histogram. (3) Set
$$\hat w_b = \frac{\hat\pi_{1,b}/\hat\pi_{0,b}}{\frac1B\sum_{b'=1}^B \hat\pi_{1,b'}/\hat\pi_{0,b'}},$$
so the weights have mean one across bins, and reweight each SNP in bin $b$ as $p_j/\hat w_b$. (4) Declare SNPs significant when $p_j/\hat w_b$ falls below the usual genome-wide threshold.

## Depends on

- [Weighted Bonferroni procedure](weighted-bonferroni-procedure.md)
- [Stratified LD-score regression](../stratified-ld-score-regression/integral-chi-sq-of-annot.md)
- [Annotation LD score of a marker](../stratified-ld-score-regression/annot-ldscore.md)

## Expansion

Step (4) is the weighted Bonferroni procedure. SNPs that tag heritability-enriched annotations have larger predicted $\chi^2$, their bins contain more non-nulls, and their p-values are made more significant; the normalization keeps the average weight at one, which is what controls the family-wise error rate. Because the weights are estimated from the data, the guarantee is approximate; it is justified when the number of estimated weights (here about 100) is much smaller than the number of tests (about $10^6$–$10^7$), and simulations at null loci showed calibration comparable to unweighted testing. Weighting by bin rather than by individual SNP prevents a single SNP's own statistic from determining its weight.

## Sources

- G. Kichaev, G. Bhatia, P.-R. Loh et al., "Leveraging polygenic functional enrichment to improve GWAS power", American Journal of Human Genetics 104 (2019), 65–75, Material and Methods, Equations 1–3, <https://doi.org/10.1016/j.ajhg.2018.11.008> (PMC6323418).
