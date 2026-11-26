# Weighted median Mendelian randomization estimator

Let $\hat\beta_{(1)} \le \dots \le \hat\beta_{(J)}$ be the ordered single-SNP
[ratio estimates](ratio-estimate.md) with positive normalized weights $w_1, \dots, w_J > 0$
satisfying $\sum_{j=1}^J w_j = 1$ (typically proportional to the
[inverse-variance weights](ivw-weight.md) $w'_j = \hat\gamma_j^2 / \sigma_{Yj}^2$).
Define the cumulative weights $s_j = \sum_{k=1}^j w_k$ and mid-point percentiles
$$p_j = s_j - \frac{w_j}{2} \qquad (j = 1, \dots, J).$$
Let $F_w : [p_1, p_J] \to \mathbb{R}$ be the continuous piecewise-linear function interpolating
the points $(p_j, \hat\beta_{(j)})$. The **weighted median Mendelian randomization estimator** is
$$\hat\beta_{\mathrm{WM}} = F_w(1/2).$$
When all weights are equal ($w_j = 1/J$), $\hat\beta_{\mathrm{WM}}$ reduces to the
[simple median estimator](simple-median-mr-estimator.md).

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)
- [Inverse-variance weight of a ratio estimate](ivw-weight.md)
- [Simple median Mendelian randomization estimator](simple-median-mr-estimator.md)

## Sources

- J. Bowden, G. Davey Smith, P. C. Haycock, and S. Burgess, "Consistent Estimation in Mendelian Randomization with Some Invalid Instruments Using a Weighted Median Estimator", Genetic Epidemiology 40 (2016), 304–314, <https://doi.org/10.1002/gepi.21965> (PMC4849733).
