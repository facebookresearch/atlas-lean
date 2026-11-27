# Zero-inflated negative binomial likelihood of the scVI generative model

For cell $n$ with batch label $s_n$ and gene $g$, single-cell variational inference (scVI) generates the count $x_{ng} \in \{0, 1, 2, \dots\}$ by

$$z_n \sim \mathcal{N}(0, I_d), \qquad \ell_n \sim \mathrm{LogNormal}(\ell_\mu, \ell_\sigma^2), \qquad \rho_n = f_w(z_n, s_n),$$

$$w_{ng} \sim \mathrm{Gamma}(\text{shape } \theta_g,\ \text{mean } \rho_{ng}), \qquad y_{ng} \mid w_{ng} \sim \mathrm{Poisson}(\ell_n w_{ng}),$$

$$h_{ng} \sim \mathrm{Bernoulli}(\pi_{ng}), \quad \pi_{ng} = f_h^g(z_n, s_n), \qquad x_{ng} = y_{ng}\,\mathbf{1}[h_{ng} = 0],$$

where $f_w$ is a neural network whose output $\rho_n$ is a vector of normalized expression frequencies, $\theta_g > 0$ is a gene-specific inverse dispersion, $\ell_\mu, \ell_\sigma$ are batch-specific (the empirical mean and variance of the log library size), and $\ell_n > 0$ is a cell-specific scaling factor. Write $\mu_{ng} = \ell_n \rho_{ng}$.

Then, given $(z_n, \ell_n, s_n)$, the counts $x_{ng}$ are independent across genes with the zero-inflated negative binomial law

$$\Pr(x_{ng} = 0) = \pi_{ng} + (1 - \pi_{ng}) \Big(\frac{\theta_g}{\theta_g + \mu_{ng}}\Big)^{\theta_g},$$

$$\Pr(x_{ng} = k) = (1 - \pi_{ng})\, \frac{\Gamma(k + \theta_g)}{\Gamma(\theta_g)\, k!} \Big(\frac{\theta_g}{\theta_g + \mu_{ng}}\Big)^{\theta_g} \Big(\frac{\mu_{ng}}{\theta_g + \mu_{ng}}\Big)^{k}, \qquad k \ge 1.$$

The negative binomial component has mean $\mu_{ng} = \ell_n \rho_{ng}$ and variance $\mu_{ng} + \mu_{ng}^2/\theta_g$. Given an observed zero, the posterior probability that it came from the Bernoulli inflation rather than the negative binomial component is

$$\frac{\pi_{ng}}{\pi_{ng} + (1 - \pi_{ng}) \big(\theta_g/(\theta_g + \mu_{ng})\big)^{\theta_g}}.$$

## Depends on

- [Negative binomial mass function with size and mean](../../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/neg-binomial-real.md)

## Proof depends on

- [The marginal law of the hierarchy is negative binomial](../../../../Probability/bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/marginal-lik-eq-neg-binomial-real.md)
- [Mean of the negative binomial law](../../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/has-sum-mul-neg-binomial-real.md)
- [Variance of the negative binomial law](../../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/variance-neg-binomial.md)

## Remarks

With rate $\beta = \theta_g/\rho_{ng}$, integrating the Poisson mass against the Gamma density gives

$$\int_0^\infty e^{-\ell w} \frac{(\ell w)^k}{k!}\, \frac{\beta^{\theta} w^{\theta - 1} e^{-\beta w}}{\Gamma(\theta)}\, dw = \frac{\Gamma(k + \theta)}{\Gamma(\theta)\, k!}\, \frac{\beta^\theta \ell^k}{(\beta + \ell)^{k + \theta}},$$

and $\beta/(\beta + \ell) = \theta/(\theta + \ell\rho)$, which is the negative binomial mass; mixing with the independent Bernoulli $h_{ng}$ adds the point mass at zero. Integrating out $w, y, h$ is what makes the likelihood $p(x_{ng} \mid z_n, \ell_n, s_n)$ available in closed form for variational inference. The library-size factor $\ell_n$ multiplies every gene's mean, so $\rho_{ng}$ is a depth-normalized, batch-conditioned expression estimate used for differential expression, while $\ell_n \rho_{ng}$ is used for imputation. On the datasets analysed, most zeros were explained by the negative binomial component, with the inflation term capturing a smaller technical share.

## Sources

- R. Lopez, J. Regier, M. B. Cole, M. I. Jordan and N. Yosef, "Deep generative modeling for single-cell transcriptomics", Nature Methods 15 (2018), 1053–1058, Online Methods (sections "The scVI probabilistic model" and "Fast inference via stochastic optimization"), <https://doi.org/10.1038/s41592-018-0229-2>, PMCID: PMC6289068.
