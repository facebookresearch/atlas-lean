# Local logistic-regression estimate of scenario posterior probabilities

**Setting.** Let $M \in \{1, \dots, J\}$ index competing population-history scenarios (for example, divergence and admixture histories of sampled populations) with prior probabilities $\pi_j$, and let $S \in \mathbb{R}^d$ be a vector of summary statistics of genetic data. A reference table $\{(m^{(r)}, s^{(r)})\}_{r=1}^{n}$ is simulated by drawing $m^{(r)} \sim \pi$, scenario parameters from their prior, and data from the coalescent under scenario $m^{(r)}$. Let $s_{\mathrm{obs}}$ be the observed statistics, $\|\cdot\|$ a (normalized) distance, and keep the $n_\delta$ simulations closest to $s_{\mathrm{obs}}$, with tolerance $\delta$ equal to the largest retained distance.

**Direct estimate.** $\widehat{P}_{\mathrm{dir}}(M = j \mid s_{\mathrm{obs}}) = \frac{1}{n_\delta}\#\{r \text{ retained} : m^{(r)} = j\}$.

**Logistic estimate.** Fit the polychotomous logistic model

$$P(M = j \mid s) = \frac{\exp\big(\beta_{j0} + \beta_j^{\top}(s - s_{\mathrm{obs}})\big)}{\sum_{l = 1}^{J} \exp\big(\beta_{l0} + \beta_l^{\top}(s - s_{\mathrm{obs}})\big)}, \qquad \beta_{10} = 0,\ \beta_1 = 0,$$

to the retained simulations by weighted maximum likelihood, with Epanechnikov weights $K_\delta(t) = \big(1 - (t/\delta)^2\big)\,\mathbf{1}\{t \le \delta\}$ applied to $t = \|s^{(r)} - s_{\mathrm{obs}}\|$, the weights of the local-linear regression adjustment of parameters. The posterior probability of scenario $j$ is estimated by the fitted model at $s = s_{\mathrm{obs}}$:

$$\widehat{P}_{\mathrm{log}}(M = j \mid s_{\mathrm{obs}}) = \frac{e^{\hat\beta_{j0}}}{\sum_{l} e^{\hat\beta_{l0}}},$$

with confidence intervals from the asymptotic normal law of the maximum-likelihood estimates.

## Depends on

- [Local-linear regression adjustment in approximate Bayesian computation](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/rejection-sampling/abc-local-linear-regression-adjustment-beaumont.md)

## Expansion

As $\delta \to 0$ and $n \to \infty$ the accepted simulations are drawn from the joint law of $(M, S)$ conditioned on $S$ near $s_{\mathrm{obs}}$, so the proportion of each scenario among them converges to $P(M = j \mid S = s_{\mathrm{obs}})$; this is the direct estimate, but at practical tolerances it depends on the arbitrary choice of $n_\delta$. Centring the covariates at $s_{\mathrm{obs}}$ makes the intercepts the log-odds at the observed point, so the regression borrows strength from simulations farther away while correcting, to first order in $s - s_{\mathrm{obs}}$, for the trend of scenario frequencies across the acceptance region. This is the classification analogue of the local-linear regression adjustment used for parameter posteriors, and the scenario indicator, being categorical, gets a logit link.

## Sources

- J.-M. Cornuet, F. Santos, M. A. Beaumont, C. P. Robert, J.-M. Marin, D. J. Balding, T. Guillemaud and A. Estoup, *Inferring population history with DIY ABC: a user-friendly approach to approximate Bayesian computation*, Bioinformatics (2008). <https://doi.org/10.1093/bioinformatics/btn514> (PMCID: PMC2639274). Section 2.3 "Comparing scenarios".
- M. A. Beaumont, W. Zhang and D. J. Balding, *Approximate Bayesian computation in population genetics*, Genetics (2002).
