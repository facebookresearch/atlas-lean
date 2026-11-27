# Liability-threshold risk given a polygenic score and family history

**Liability threshold model.** Each individual has a standard normal liability $\epsilon$ and is a case ($Z = 1$) iff $\epsilon \ge T$, so the prevalence is $K = 1 - \Phi(T)$ with $\Phi$ the standard normal distribution function and $\varphi$ its density.

**Joint model.** For a target individual $o$ with polygenic score $\mathrm{PRS}_o$, parents $p_1, p_2$ and a sibling $s$, assume

$$\begin{pmatrix}\epsilon_o \\ \mathrm{PRS}_o \\ \epsilon_{p_1} \\ \epsilon_{p_2} \\ \epsilon_s\end{pmatrix} \sim \mathcal N_5\left(0,\ \begin{pmatrix} 1 & V & \tilde h_{p_1}^2/2 & \tilde h_{p_2}^2/2 & \tilde h_s^2/2 \\ V & V & V/2 & V/2 & V/2 \\ \tilde h_{p_1}^2/2 & V/2 & 1 & 0 & \tilde h_{p_1}^2/2 \\ \tilde h_{p_2}^2/2 & V/2 & 0 & 1 & \tilde h_{p_2}^2/2 \\ \tilde h_s^2/2 & V/2 & \tilde h_{p_1}^2/2 & \tilde h_{p_2}^2/2 & 1 \end{pmatrix}\right),$$

where $V$ is the liability-scale variance explained by the score (the score is rescaled to have variance $V$) and the pseudo-heritabilities $\tilde h^2$ absorb heritability and shared environment for each class of relative; setting all $\tilde h^2 = h^2$ assumes no environmental correlation.

**Score calibration.** With $Z$ the case indicator in the target population,

$$V = \mathrm{corr}(\mathrm{PRS}, Z)^2\, \frac{K(1 - K)}{\varphi(T)^2}.$$

**Posterior risk.** Conditioning the joint law on $\mathrm{PRS}_o$ and on each relative's status ($\epsilon_r \ge T_r$ for an affected relative, $\epsilon_r < T_r$ otherwise) gives a posterior mean $\mu_{\epsilon_o \mid \cdot}$ and variance $\sigma^2_{\epsilon_o \mid \cdot}$ for the target's liability, computed by the Pearson–Aitken selection formulas and truncated-normal moments; treating the posterior as normal, the predicted risk is

$$r = 1 - \Phi\Big(\frac{T_{\mathrm{offspring}} - \mu_{\epsilon_o \mid \cdot}}{\sigma_{\epsilon_o \mid \cdot}}\Big),$$

with threshold $T_{\mathrm{offspring}} = \Phi^{-1}(1 - K_{\mathrm{offspring}})$ or a covariate-dependent threshold. Missing relatives are handled by dropping their rows and columns.

## Depends on

- [Liability-scale R² of a jointly Gaussian score from its observed R²](../corr-sq-liability-eq.md): the score calibration $V = \mathrm{corr}(\mathrm{PRS}, Z)^2 K(1-K)/\varphi(T)^2$
- [Prevalence of the threshold model](../prevalence.md): $K = 1 - \Phi(T)$
- [Standard normal density at the threshold](../threshold-density.md): $\varphi(T)$
- [Gaussian conditioning (Schur complement)](../../../../Probability/distributions/continuous/gaussian-conditioning/cond-distrib-multivariate-gaussian.md): conditioning the joint law on $\mathrm{PRS}_o$
- [Response to truncation selection on a Gaussian score](../../../../Probability/not-yet-classified/part-06/gaussian-selection/conditional-mean-shift-standardized-uppe.md): the Pearson–Aitken update for an affected relative
- [Standard normal CDF](../../../../Probability/central-limit-theorems/berry-esseen-theorem/kolmogorov-distance/normal-cdf.md): $\Phi$ in the predicted risk

## Expansion

The covariance entries follow from additive inheritance: a parent shares half of the target's additive genetic value, so $\mathrm{Cov}(\epsilon_o, \epsilon_p) = \tilde h_p^2/2$ and $\mathrm{Cov}(\mathrm{PRS}_o, \epsilon_p) = V/2$, while unrelated parents have independent liabilities. Conditioning on an affected relative is a truncation, after which the target's liability is no longer exactly Gaussian; the normal approximation in the risk formula is usually accurate, and using the posterior risk rather than the posterior mean liability weights mean and variance correctly. The calibration of $V$ is the observed-to-liability conversion for a score jointly Gaussian with liability. The threshold matches the convention $K = 1 - \Phi(T)$ above: with no information ($\mu = 0$, $\sigma = 1$) the predicted risk is $K_{\mathrm{offspring}}$; the source writes $\Phi^{-1}(K_{\mathrm{offspring}})$, which under this convention would give $1 - K_{\mathrm{offspring}}$. In UK Biobank, adding parental and sibling history to a European-trained score raised liability-scale $R^2$ far more in South Asian and African target samples than in Europeans, because family history transfers across ancestries while the score does not; a logistic model with the same inputs performed better when covariates were included.

## Sources

- M. L. A. Hujoel, P.-R. Loh, B. M. Neale and A. L. Price, "Incorporating family history of disease improves polygenic risk scores in diverse populations", Cell Genomics 2 (2022), 100152, STAR Methods ("PRS-FHliab", Eqs. (3)–(5)), <https://doi.org/10.1016/j.xgen.2022.100152>, PMCID PMC9351615.
