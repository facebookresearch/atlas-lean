# Genomic control inflation factor

**Setting.** A genome-wide association study produces 1-degree-of-freedom statistics $T_1, \dots, T_M$ (squared $z$-scores of allelic effects) at $M$ markers. Under no association and no confounding, each $T_k \sim \chi^2_1$, whose median is $m_1 = (\Phi^{-1}(3/4))^2 \approx 0.4549$. Population stratification or cryptic relatedness multiplies the null statistics by a common factor $\lambda \ge 1$ in the genomic control model, $T_k \approx \lambda\,\chi^2_1$ for null markers.

**Estimator and correction.** The genomic control estimator is the raw median ratio

$$\hat\lambda = \frac{\operatorname{median}(T_1, \dots, T_M)}{m_1},$$

which can be below $1$ in a sample even though the model's $\lambda \ge 1$. The correction uses the floored factor $\tilde\lambda = \max(\hat\lambda, 1)$ throughout:

$$T_k^{\mathrm{GC}} = \frac{T_k}{\tilde\lambda}, \qquad V^{\mathrm{GC}} = \tilde\lambda\, V,$$

and the two forms agree, since $T_k = \hat\beta_k^2 / V_k$ for the effect estimate $\hat\beta_k$ with variance $V_k$. With $\hat\lambda < 1$ both leave the statistics unchanged; using the raw $\hat\lambda$ in one form and the floored factor in the other would not be equivalent (for $\hat\lambda = 0.8$, $V' = 0.8\,V$ would raise $T_k$ by $25\%$ while $T_k / \max(\hat\lambda, 1)$ leaves it unchanged).

**Use in meta-analysis.** Before inverse-variance meta-analysis each study $i$ can be corrected by its own floored factor, computed separately for directly genotyped and imputed markers ($\tilde\lambda_{D_i}$, $\tilde\lambda_{D_i^*}$, each the maximum of $1$ and the raw median estimate in that class), so that $V_{ij}^{\mathrm{GC}} = \tilde\lambda_{K_i} V_{ij}$ with $K \in \{D, D^*\}$; a second, genome-wide factor computed in the same way from the meta-analysis statistics can then correct for residual between-study inflation.

## Remarks

If at most a small fraction of markers is truly associated, the median of $T_1, \dots, T_M$ is a robust estimate of the median of the null law $\lambda\chi^2_1$, which is $\lambda m_1$; dividing by $\hat\lambda$ restores the nominal null distribution; flooring the factor at $1$ means the correction never makes statistics larger. The floor is the convention of Devlin and Roeder; the GWAMA description inflates each variance by the raw median factor without stating a floor, which with $\hat\lambda < 1$ would shrink the variances and enlarge the statistics, so an implementation must fix one convention for both the statistic and the variance. The median is preferred to the mean because a polygenic or strongly associated minority of markers moves it little. The correction assumes the inflation is uniform across markers; it over-corrects when inflation is due to true polygenic signal, the distinction that LD-score regression later addressed.

## Depends on

- [Common-inflation model of Gaussian null scores](../../../genomic-control/common-inflation-model.md)

## Sources

- R. Mägi and A. P. Morris, "GWAMA: software for genome-wide association meta-analysis", BMC Bioinformatics 11 (2010), 288, Implementation ("Correcting for population structure"), <https://doi.org/10.1186/1471-2105-11-288>, PMCID PMC2893603.
- B. Devlin and K. Roeder, "Genomic control for association studies", Biometrics 55 (1999), 997–1004, <https://doi.org/10.1111/j.0006-341X.1999.00997.x>.
