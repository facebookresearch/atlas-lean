# Weighted median Mendelian randomization estimator

Let $\hat\beta_{(1)} \le \dots \le \hat\beta_{(J)}$ be the ordered single-SNP
[ratio estimates](ratio-estimate.md) of $J \ge 1$ variants, and let $w_j > 0$ be the normalized weight of the
variant whose estimate is $\hat\beta_{(j)}$, so that $\sum_{j=1}^J w_j = 1$ (typically $w_j$ is proportional to
the [inverse-variance weight](ivw-weight.md) $w'_j = \hat\beta_{Xj}^2 / \sigma_j^2$). Define the cumulative
weights $s_j = \sum_{k=1}^j w_k$ and the mid-point percentiles

$$p_j = s_j - \frac{w_j}{2} \qquad (j = 1, \dots, J).$$

Then $p_1 = w_1/2 \le 1/2$ and $p_J = 1 - w_J/2 \ge 1/2$. Let $F_w : [p_1, p_J] \to \mathbb{R}$ be the
continuous piecewise-linear function interpolating the points $(p_j, \hat\beta_{(j)})$. The
**weighted median Mendelian randomization estimator** (the interpolated weighted median of Bowden et al.) is

$$\hat\beta_{\mathrm{WM}} = F_w(1/2).$$

Tied estimates are listed in a fixed but arbitrary order. When all weights are equal
($w_j = 1/J$), $\hat\beta_{\mathrm{WM}}$ reduces to the [simple median estimator](simple-median-mr-estimator.md).

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)
- [Inverse-variance weight of a ratio estimate](ivw-weight.md)
- [Simple median Mendelian randomization estimator](simple-median-mr-estimator.md)

## Sources

- J. Bowden, G. Davey Smith, P. C. Haycock, and S. Burgess, "Consistent Estimation in Mendelian Randomization with Some Invalid Instruments Using a Weighted Median Estimator", Genetic Epidemiology 40 (2016), 304–314, <https://doi.org/10.1002/gepi.21965> (PMC4849733).
