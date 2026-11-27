# Genomic control inflation factor

**Setting.** A genome-wide association study produces 1-degree-of-freedom statistics $T_1, \dots, T_M$ (squared $z$-scores of allelic effects) at $M$ markers. Under no association and no confounding, each $T_k \sim \chi^2_1$, whose median is $m_1 = (\Phi^{-1}(3/4))^2 \approx 0.4549$. Under the [common-inflation model](../../../genomic-control/common-inflation-model.md), population stratification or cryptic relatedness multiplies the null statistics by a common factor $\lambda > 0$, so $T_k \approx \lambda\,\chi^2_1$ for null markers.

**Estimator and correction.** The genomic control estimator is the median ratio

$$\hat\lambda = \frac{\operatorname{median}(T_1, \dots, T_M)}{m_1}.$$

In GWAMA, each study's effect-estimate variance $V$ is inflated by $\hat\lambda$, and equivalently each 1-degree-of-freedom statistic $T_k = \hat\beta_k^2 / V_k$ is divided by $\hat\lambda$:

$$T_k^{\mathrm{GC}} = \frac{T_k}{\hat\lambda}, \qquad V^{\mathrm{GC}} = \hat\lambda\, V.$$

**Use in meta-analysis.** Before inverse-variance meta-analysis each study $i$ can be corrected by its own inflation factor, computed separately for directly genotyped and imputed markers ($\hat\lambda_{D_i}$, $\hat\lambda_{D_i^*}$), so that $V_{ij}^{\mathrm{GC}} = \hat\lambda_{K_i} V_{ij}$ with $K \in \{D, D^*\}$; a second, genome-wide factor computed in the same way from the meta-analysis statistics can then correct for residual between-study inflation.

## Remarks

If at most a small fraction of markers is truly associated, the median of $T_1, \dots, T_M$ is a robust estimate of the median of the null law $\lambda\chi^2_1$, which is $\lambda m_1$; dividing by $\hat\lambda$ restores the nominal null distribution. The GWAMA formulation uses the raw median factor $\hat\lambda$ directly without stating a floor at $1$ (in practice, when $\hat\lambda < 1$, some implementations instead apply $\max(\hat\lambda, 1)$ to both $T_k$ and $V$ so that statistics are never enlarged; the same convention must be applied consistently to both). The median is preferred to the mean because a polygenic or strongly associated minority of markers moves it little. The correction assumes the inflation is uniform across markers; it over-corrects when inflation is due to true polygenic signal, the distinction that LD-score regression later addressed.

## Depends on

- [Common-inflation model of Gaussian null scores](../../../genomic-control/common-inflation-model.md)

## Sources

- R. Mägi and A. P. Morris, "GWAMA: software for genome-wide association meta-analysis", BMC Bioinformatics 11 (2010), 288, Implementation ("Correcting for population structure"), <https://doi.org/10.1186/1471-2105-11-288>, PMCID PMC2893603.
