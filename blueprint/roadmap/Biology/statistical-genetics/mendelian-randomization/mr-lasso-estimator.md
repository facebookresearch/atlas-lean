# MR-Lasso estimator

Let $J$ independent variants have summary estimates $\hat\beta_{Xj}$ (variant–exposure) and $\hat\beta_{Yj}$ (variant–outcome) with outcome standard errors $\sigma_{Yj}$. The [inverse-variance-weighted estimator](ivw.md) minimizes $\sum_j \sigma_{Yj}^{-2} (\hat\beta_{Yj} - \theta \hat\beta_{Xj})^2$. MR-Lasso adds a variant-specific intercept $\theta_{0j}$, the direct (pleiotropic) effect of variant $j$ on the outcome, and minimizes

$$\sum_{j=1}^{J} \sigma_{Yj}^{-2} \bigl(\hat\beta_{Yj} - \theta_{0j} - \theta \hat\beta_{Xj}\bigr)^2 + \lambda \sum_{j=1}^{J} |\theta_{0j}|$$

over $(\theta, \theta_{01}, \dots, \theta_{0J})$ for a tuning parameter $\lambda > 0$. The causal estimate is the IVW estimate computed on the variants with $\hat\theta_{0j} = 0$. The paper increases $\lambda$ step by step and stops one step before the retained variants show more heterogeneity of their ratio estimates than expected by chance.

## Depends on

- [Inverse-variance-weighted estimator](ivw.md)

## Expansion

Without the penalty the model has $J + 1$ parameters for $J$ observations and is not identified; the $\ell_1$ penalty sets most intercepts exactly to zero, so valid instruments (zero direct effect) are kept and outlying, likely pleiotropic variants receive nonzero intercepts and are dropped. The method is consistent under the IVW assumptions for the retained set.

## Sources

- E. A. W. Slob and S. Burgess, *A comparison of robust Mendelian randomization methods using summary data*, Genet. Epidemiol. 44 (2020), 313–329. <https://doi.org/10.1002/gepi.22295> (PMCID: PMC7317850) Methods, "Outlier-robust methods", Equations (5) and (6).
