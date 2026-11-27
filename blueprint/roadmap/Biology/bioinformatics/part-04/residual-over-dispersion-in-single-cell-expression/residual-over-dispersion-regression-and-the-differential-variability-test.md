# Residual over-dispersion regression and the differential variability test

Let $X_{ij}$ be the count of gene $i \in \{1,\dots,q_0\}$ in cell $j \in \{1,\dots,n\}$. In the hierarchical Poisson–gamma model

$$X_{ij} \mid \mu_i, \phi_j, \nu_j, \rho_{ij} \sim \mathrm{Poisson}(\phi_j \nu_j \mu_i \rho_{ij}), \qquad \nu_j \sim \mathrm{Gamma}\!\Big(\tfrac1\theta, \tfrac{1}{s_j \theta}\Big), \qquad \rho_{ij} \sim \mathrm{Gamma}\!\Big(\tfrac1{\delta_i}, \tfrac1{\delta_i}\Big),$$

$\mu_i > 0$ is the mean expression of gene $i$, $\phi_j, s_j$ are cell-specific normalization factors, $\theta$ is global technical noise, and $\delta_i > 0$ is the biological **over-dispersion** of gene $i$, its excess variability beyond Poisson and technical noise.

**Mean–dispersion regression prior.** Take $\mu_i \sim \log\text{-}\mathcal N(0, s_\mu^2)$ and

$$\log \delta_i = f(\mu_i) + \epsilon_i, \qquad \epsilon_i \sim t_\eta(0, \sigma^2),$$

$$f(\mu) = \alpha_0 + \alpha_1 \log\mu + \sum_{l=1}^{L} \beta_l \exp\!\Big\{-\tfrac12\Big(\tfrac{\log\mu - m_l}{h_l}\Big)^2\Big\},$$

a linear trend plus $L$ Gaussian radial basis functions with fixed centres $m_l$ and widths $h_l$, with $\beta \mid \sigma^2 \sim \mathcal N(m_\beta, \sigma^2 V_\beta)$ and $\sigma^2 \sim \text{Inv-Gamma}(a_{\sigma^2}, b_{\sigma^2})$. The latent $\epsilon_i$ is the **residual over-dispersion**: positive values mean more variability than genes of similar mean.

**Decomposition.** For two populations $A, B$,

$$\log_2\frac{\delta_i^A}{\delta_i^B} = \log_2(e)\Big[\underbrace{f^A(\mu_i^A) - f^B(\mu_i^B)}_{\text{mean contribution}} + \underbrace{\epsilon_i^A - \epsilon_i^B}_{\text{residual change}}\Big].$$

**Decision rule.** Gene $i$ is called differentially variable when $\mathbb P(|\epsilon_i^A - \epsilon_i^B| > \psi_0 \mid \text{data}) > \alpha_R$ for a tolerance $\psi_0 > 0$, or, for $\psi_0 = 0$, when $2\max\{\pi_i, 1 - \pi_i\} - 1 > \alpha_R$ with $\pi_i = \mathbb P(\epsilon_i^A - \epsilon_i^B > 0 \mid \text{data})$; the threshold $\alpha_R$ is calibrated to a target expected false discovery rate.

## Depends on

- [The marginal law of the hierarchy is negative binomial](../../../../Probability/bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/marginal-lik-eq-neg-binomial-real.md)

## Expansion

Integrating out $\rho_{ij}$ gives a negative binomial likelihood, and writing the prior as $\delta_i \sim \log\text{-}t_\eta(f(\mu_i), \sigma^2)$ with the scale-mixture representation $\epsilon_i \mid \lambda_i \sim \mathcal N(0, \sigma^2/\lambda_i)$, $\lambda_i \sim \mathrm{Gamma}(\eta/2, \eta/2)$ makes $\beta$, $\sigma^2$, $\lambda_i$ conjugate, so the posterior is sampled by adaptive Metropolis-within-Gibbs. Heavy $t$ tails (default $\eta = 5$) keep outlying genes from distorting the trend, and the linear term stabilizes the fit where few genes have a given mean. Under $\psi_0 = 0$ the two-sided tail probability is identically one, hence the switch to the maximum of the one-sided posterior probabilities.

## Sources

- N. Eling, A. C. Richard, S. Richardson, J. C. Marioni, C. A. Vallejos, "Correcting the mean-variance dependency for differential variability testing using single-cell RNA sequencing data", Cell Systems 7(3) (2018) 284–294, STAR Methods, Equations 1–8 and 33–35, <https://doi.org/10.1016/j.cels.2018.06.011>, PMCID PMC6167088.
