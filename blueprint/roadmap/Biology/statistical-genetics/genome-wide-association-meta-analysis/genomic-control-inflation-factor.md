# Genomic control inflation factor

**Setting.** A genome-wide association study produces 1-degree-of-freedom statistics $T_1, \dots, T_M$ (squared $z$-scores of allelic effects) at $M$ markers. Under no association and no confounding, each $T_k \sim \chi^2_1$, whose median is $m_1 = (\Phi^{-1}(3/4))^2 \approx 0.4549$. Population stratification or cryptic relatedness multiplies the null statistics by a common factor $\lambda \ge 1$ in the genomic control model, $T_k \approx \lambda\,\chi^2_1$ for null markers.

**Estimator and correction.**

$$\hat\lambda = \frac{\operatorname{median}(T_1, \dots, T_M)}{m_1}, \qquad T_k^{\mathrm{GC}} = \frac{T_k}{\max(\hat\lambda, 1)}.$$

Equivalently the variance of each effect estimate is multiplied by $\hat\lambda$, $V^{\mathrm{GC}} = \hat\lambda V$.

**Use in meta-analysis.** Before inverse-variance meta-analysis each study $i$ can be corrected by its own factor, computed separately for directly genotyped and imputed markers ($\lambda_{D_i}$, $\lambda_{D_i^*}$), so that $V_{ij}^{\mathrm{GC}} = \lambda_{K_i} V_{ij}$ with $K \in \{D, D^*\}$; a second, genome-wide factor computed from the meta-analysis statistics can then correct for residual between-study inflation.

## Expansion

If at most a small fraction of markers is truly associated, the median of $T_1, \dots, T_M$ is a robust estimate of the median of the null law $\lambda\chi^2_1$, which is $\lambda m_1$; dividing by $\hat\lambda$ restores the nominal null distribution. The median is preferred to the mean because a polygenic or strongly associated minority of markers moves it little. The correction assumes the inflation is uniform across markers; it over-corrects when inflation is due to true polygenic signal, the distinction that LD-score regression later addressed.

## Sources

- R. Mägi and A. P. Morris, "GWAMA: software for genome-wide association meta-analysis", BMC Bioinformatics 11 (2010), 288, Implementation ("Correcting for population structure"), <https://doi.org/10.1186/1471-2105-11-288>, PMCID PMC2893603.
- B. Devlin and K. Roeder, "Genomic control for association studies", Biometrics 55 (1999), 997–1004, <https://doi.org/10.1111/j.0006-341X.1999.00997.x>.
