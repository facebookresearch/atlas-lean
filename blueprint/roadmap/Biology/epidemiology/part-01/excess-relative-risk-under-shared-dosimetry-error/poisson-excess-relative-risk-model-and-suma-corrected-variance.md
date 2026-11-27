# Poisson excess relative risk model and the SUMA-corrected variance

**ERR model.** For person-year $i$ with follow-up time $t_i$, exposures $X_{1,i}$ (uncertain dose) and $X_{2,i}$ (known dose), background covariates $C_{\cdot,i}$ and effect modifiers $A_{\cdot,i}$, the hazard is

$$h_i = \exp(a_0 + a_1C_{1,i} + a_2C_{2,i} + a_3C_{3,i})\big(1 + b_1X_{1,i}\exp(a_4A_{1,i} + a_5A_{2,i}) + b_2X_{2,i}\big),$$

an instance of $h(t) = \mathrm{background}(t)\,(1 + \sum_i b_iX_i(t)\,\mathrm{modifier}_i(t))$; event counts are Poisson with mean $t_ih_i$ (the piecewise-exponential survival likelihood equals the Poisson likelihood up to a constant).

**SUMA dose-error model.** The true dose $X_i$ relates to its Monte Carlo mean $Z_i = E(X_i)$ (a Berkson model) through shared (S) and unshared, multiplicative (M) and additive (A) errors,

$$X_i = \epsilon_{SM}\,\epsilon_{M,i}\,Z_i + \epsilon_{SA} + \epsilon_{A,i}, \qquad E\epsilon_{SM} = E\epsilon_{M,i} = 1,\; E\epsilon_{SA} = E\epsilon_{A,i} = 0.$$

**Proposition (corrected variance).** Fit the model with $Z_1$ in place of $X_1$ and let $\theta = (a_0,a_1,a_2,a_3,b_1,a_4,a_5,b_2)$, $I_{Z_1}$ the Fisher information and $S_{Z_1}$ the score. Then $\hat\theta - \theta \approx I_{Z_1}^{-1}S_{Z_1}$, $\operatorname{Var}(S_{Z_1}) = I_{Z_1} + b_1^2\,QG\operatorname{Cov}(X_1\mid Z_1)GQ^{\mathsf T}$, and with $M = QG$

$$\operatorname{Var}(\hat\theta) \approx I_{Z_1}^{-1} + b_1^2\,I_{Z_1}^{-1}M\operatorname{Cov}(X_1\mid Z_1)M^{\mathsf T}I_{Z_1}^{-1},$$

where $G = \operatorname{diag}\big(t_i e^{a_0 + a_1C_{1,i}+a_2C_{2,i}+a_3C_{3,i}}\big)$ and the columns $Q_i$ of $Q$ are the derivatives of $\log(\text{rate})$ with respect to $\theta$ evaluated at $Z_{1,i}$.

**Computation.** With an $n\times k$ matrix $\mathbf X_1$ of $k$ Monte Carlo dose replicates, the sample covariance of $W = M\mathbf X_1$ equals $M\widehat{\operatorname{Cov}}(X_1\mid Z_1)M^{\mathsf T}$, at cost $\Theta(pnk + p^2k)$ instead of $\Theta(n^2k + p^2n^2)$.

## Depends on

- [Poisson likelihood](../../../../Probability/hypothesis-testing/monotone-likelihood-ratio/poisson-lik.md)
- [Fisher information](../../../../Probability/statistical-estimation/fisher-information-and-the-cram-r-rao-bound/fisher-information.md)

## Expansion

The score is linear in the observed counts, whose conditional mean depends on the true dose; averaging over the dose replicates adds to the Poisson variance a term quadratic in $b_1$ through the dose covariance, which is dense when errors are shared. Wald intervals with this variance ignore that it grows with $b_1$; score-type intervals that plug the null value into the variance can become unbounded, because the test statistic tends to a finite limit as $b_1^* \to \pm\infty$.

## Sources

- Z. Zhang, D. L. Preston, M. Sokolnikov, B. A. Napier, M. Degteva, B. Moroz, V. Vostrotin, E. Shiskina, A. Birchall, D. O. Stram, "Correction of confidence intervals in excess relative risk models using Monte Carlo dosimetry systems with shared errors", PLoS ONE 12(4) (2017) e0174641, Data and methods, Eq (1), SUMA model, Eqs (2)–(4) and the efficient-calculation identity, <https://doi.org/10.1371/journal.pone.0174641>, PMCID PMC5378348.
