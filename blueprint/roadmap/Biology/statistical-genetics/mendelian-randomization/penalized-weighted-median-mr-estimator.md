# Penalized weighted median Mendelian randomization estimator

Given single-SNP ratio estimates $\hat\beta_j$ with unnormalized inverse-variance weights
$w'_j > 0$ and the [weighted median estimate](weighted-median-mr-estimator.md) $\hat\beta_{\mathrm{WM}}$,
define each variant's heterogeneity statistic

$$Q_j = w'_j \bigl(\hat\beta_j - \hat\beta_{\mathrm{WM}}\bigr)^2,$$

and let $q_j = \mathbb{P}(\chi_1^2 \ge Q_j)$ be its upper-tail $\chi_1^2$ probability.
The **penalized weights** are

$$w_j^{\mathrm{pen}} = \frac{w'_j \min(1, 20\,q_j)}{\sum_{k=1}^J w'_k \min(1, 20\,q_k)},$$

and the **penalized weighted median estimator** is the weighted median computed with weights
$w_j^{\mathrm{pen}}$. Variants with $q_j \ge 0.05$ retain full relative weight, while severely
heterogeneous outliers are downweighted continuously toward zero.

## Depends on

- [Weighted median Mendelian randomization estimator](weighted-median-mr-estimator.md)

## Sources

- J. Bowden, G. Davey Smith, P. C. Haycock, and S. Burgess, "Consistent Estimation in Mendelian Randomization with Some Invalid Instruments Using a Weighted Median Estimator", Genetic Epidemiology 40 (2016), 304–314, <https://doi.org/10.1002/gepi.21965> (PMC4849733).
