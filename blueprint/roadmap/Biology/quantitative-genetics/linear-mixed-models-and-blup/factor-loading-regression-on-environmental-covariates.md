# Factor-loading regression on environmental covariates for prediction in new environments

**Multi-environment factor model (MegaLMM).** Let $Y$ be an $n \times t$ matrix of one trait measured on $n$ genotypes in $t$ trials, possibly with many missing entries. Model

$$Y = F\Lambda + E,$$

with $F$ an $n \times k$ matrix of latent factors (unobserved traits of each genotype, constant across trials), $\Lambda$ a $k \times t$ matrix of trial-specific loadings, and $E$ residuals. Each factor $f_k$ and each residual column $e_j$ gets its own univariate linear mixed model,

$$f_k = Xb_{Fk} + Zu_{Fk} + e_{Fk}, \qquad e_j = Xb_{Rj} + Zu_{Rj} + e_{Rj},$$

$$u_{Fk} \sim N(0, \sigma^2_{gFk}K), \quad u_{Rj} \sim N(0, \sigma^2_{gRj}K), \quad e_{Fk} \sim N(0, \sigma^2_{eFk}I), \quad e_{Rj} \sim N(0, \sigma^2_{eRj}I),$$

with $K$ the genomic relationship matrix. The correlated $t$-trait mixed model thus splits into $k + t$ independent univariate ones. Parameters are fitted by Gibbs sampling.

**Loadings regressed on environmental covariates.** With independent priors on the columns of $\Lambda$, loadings for an unobserved environment cannot be learned. The extension instead regresses each row of loadings on $L$ environmental-covariate design matrices $W_l$ (intercept, location, tester, or quantitative weather covariates):

$$\lambda_{k\cdot} = \sum_{l=1}^{L} W_l\,a_{lk} + \epsilon_k, \qquad a_{lk} \sim N(0, \sigma_{lk}^2\tau_k^{-1}I), \qquad \epsilon_{kj} \sim N(0, \psi_{jk}^{-1}\tau_k^{-1}),$$

with $\sigma_l^2 \sim \mathrm{invGamma}(a,b)$, $\psi_{jk} \sim \mathrm{Ga}(\nu/2, \nu/2)$, and a multiplicative-gamma shrinkage $\tau_k = \prod_{h \le k}\delta_h$ that shrinks higher-order factors towards zero.

**Predictions.** For old genotypes in a new environment with covariates $W_l^{n}$, posterior samples of genetic values are

$$G_{on} = F\Big(\sum_{l=1}^{L} W_l^{n}a_{lk}\Big)^{\!\top}.$$

For new genotypes, $F$ is replaced by the kriged factors $F_n = K_{no}K^{-1}F$, where $K_{no}$ is the relationship matrix between new and old genotypes.

## Depends on

- [BLUP is the conditional expectation](cond-exp-mixed-model.md)

## Expansion

The factor decomposition makes the genetic covariance across trials $\Lambda^\top\operatorname{diag}(\sigma^2_{gFk})\Lambda$ plus a diagonal residual-genetic part, a low-rank-plus-diagonal structure that scales to many trials. Writing the loadings as a regression on covariates links trials through their covariates rather than only through shared genotypes. Covariate values for a new environment therefore yield its loadings, and multiplying by the genotype factors yields predictions. The kriging step $K_{no}K^{-1}F$ is the conditional mean of a Gaussian random effect at new genotypes given its values at old ones. It is the same calculation that makes BLUP a conditional expectation. In the paper's maize multi-environment data, quantitative environmental covariates could substitute for qualitative ones (such as location identity) in predicting performance in new environments.

## Sources

- H. Hu, R. Rincent and D. E. Runcie, "MegaLMM improves genomic predictions in new environments using environmental covariates", *Genetics* (2024), iyae171, <https://doi.org/10.1093/genetics/iyae171> (PMC11708919), Materials and methods (Equations 1–5, "Original MegaLMM model" and "Extensions to predict trait performance in new environments") and Results.
