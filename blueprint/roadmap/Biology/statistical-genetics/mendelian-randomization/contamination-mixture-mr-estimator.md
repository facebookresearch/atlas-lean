# Contamination mixture estimator for Mendelian randomization

Let $J$ genetic variants have [ratio estimates](ratio-estimate.md) $\hat\theta_j$ with standard errors $\mathrm{se}(\hat\theta_j)$, treated as fixed and known (variants strongly associated with the risk factor, so $\hat\theta_j$ is approximately normal). Model each estimate as a two-component mixture:

$$\hat\theta_j \sim N\big(\theta, \mathrm{se}(\hat\theta_j)^2\big) \ \text{if variant } j \text{ is a valid instrument}, \qquad \hat\theta_j \sim N\big(0, \psi^2 + \mathrm{se}(\hat\theta_j)^2\big) \ \text{otherwise},$$

where invalid variants estimate other values $\theta_{F,j} \sim N(0,\psi^2)$ and $\psi > 0$ is a fixed dispersion parameter. With a configuration $\zeta \in \{0,1\}^J$ ($\zeta_j = 1$ iff $j$ is valid), the likelihood is

$$L(\theta,\zeta) = \prod_{j=1}^J\Big[\zeta_j\,\frac{1}{\sqrt{2\pi\,\mathrm{se}(\hat\theta_j)^2}}\exp\Big(-\frac{(\theta-\hat\theta_j)^2}{2\,\mathrm{se}(\hat\theta_j)^2}\Big) + (1-\zeta_j)\,\frac{1}{\sqrt{2\pi(\psi^2 + \mathrm{se}(\hat\theta_j)^2)}}\exp\Big(-\frac{\hat\theta_j^2}{2(\psi^2 + \mathrm{se}(\hat\theta_j)^2)}\Big)\Big].$$

**Profile likelihood.** For fixed $\theta$ the maximizing configuration is $\hat\zeta^\theta_j = \mathbf 1\{L_{V,j}(\theta) > L_{F,j}\}$, comparing the valid and invalid factors of variant $j$, so $L_p(\theta) = L(\theta,\hat\zeta^\theta) = \prod_j \max\{L_{V,j}(\theta), L_{F,j}\}$ is computed in $O(J)$ per value of $\theta$ instead of $O(2^J)$. The estimate is $\hat\theta_p = \arg\max_\theta L_p(\theta)$, and the $95\%$ confidence set is

$$\big\{\theta : 2[\log L_p(\hat\theta_p) - \log L_p(\theta)] \le \chi^2_{1,0.95}\big\},$$

which need not be symmetric or connected (disjoint pieces indicate groups of variants with distinct causal estimates). To allow overdispersion among the selected valid variants, $\chi^2_{1,0.95}$ is replaced by $\max(1,\hat\phi^2)\chi^2_{1,0.95}$, with $\hat\phi$ the residual standard error of the inverse-variance-weighted regression on the selected variants. $L_p$ is continuous in $\theta$ because $\hat\zeta^\theta_j$ switches only where $L_{V,j}(\theta) = L_{F,j}$.

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)
- [Inverse-variance-weighted estimator](ivw.md)

## Expansion

The likelihood factorizes over variants given $(\theta,\zeta)$, so the inner maximization over $\zeta$ decouples into $J$ independent binary choices; the profile log-likelihood is a sum of pointwise maxima of a concave quadratic in $\theta$ and a constant, hence piecewise quadratic and possibly multimodal. A variant is classed valid exactly when $|\theta - \hat\theta_j|$ is small relative to its standard error, which bounds the influence of outlying (pleiotropic) variants. The interval inverts Wilks' likelihood-ratio test; the authors recommend a sensitivity analysis in $\psi$, starting from $1.5$ times the standard deviation of the ratio estimates.

## Sources

- Stephen Burgess, Christopher N. Foley and Elias Allara, "A robust and efficient method for Mendelian randomization with hundreds of genetic variants", Nature Communications (2020), <https://doi.org/10.1038/s41467-019-14156-4> (PMC6969055). Methods, "Contamination mixture method", Eqs. (5)–(9).
