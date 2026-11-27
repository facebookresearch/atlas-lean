# Penalized weighted median Mendelian randomization estimator

Let $\hat\beta_1, \dots, \hat\beta_J$ be single-SNP [ratio estimates](ratio-estimate.md) with positive
[inverse-variance weights](ivw-weight.md) $w'_1, \dots, w'_J > 0$, and let $\hat\beta_{\mathrm{IVW}}$ be the
[inverse-variance-weighted estimate](ivw.md). Define each variant's heterogeneity statistic, centred on the
IVW estimate,

$$Q_j = w'_j \bigl(\hat\beta_j - \hat\beta_{\mathrm{IVW}}\bigr)^2,$$

and let $q_j = \mathbb{P}(\chi_1^2 \ge Q_j) \in (0, 1]$ be its upper-tail probability under the
[chi-square law](../../../Probability/distributions/continuous/chi-square-distribution/chi-square-measure.md)
with one degree of freedom.
The **penalized weights** are

$$w_j^{\mathrm{pen}} = \frac{w'_j \min(1, 20\,q_j)}{\sum_{k=1}^J w'_k \min(1, 20\,q_k)},$$

whose denominator is positive, and the **penalized weighted median estimator** is the
[weighted median estimate](weighted-median-mr-estimator.md) computed from $\hat\beta_1, \dots, \hat\beta_J$
with the weights $w_j^{\mathrm{pen}}$. Variants with $q_j \ge 0.05$ keep their relative weight, while
heterogeneous outliers are downweighted continuously toward zero.

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)
- [Inverse-variance weight of a ratio estimate](ivw-weight.md)
- [Inverse-variance-weighted estimator](ivw.md)
- [Weighted median Mendelian randomization estimator](weighted-median-mr-estimator.md)
- [Chi-square distribution](../../../Probability/distributions/continuous/chi-square-distribution/chi-square-measure.md)

## Sources

- J. Bowden, G. Davey Smith, P. C. Haycock, and S. Burgess, "Consistent Estimation in Mendelian Randomization with Some Invalid Instruments Using a Weighted Median Estimator", Genetic Epidemiology 40 (2016), 304–314, <https://doi.org/10.1002/gepi.21965> (PMC4849733). (Section "Penalized Weighted Median Estimator".)
