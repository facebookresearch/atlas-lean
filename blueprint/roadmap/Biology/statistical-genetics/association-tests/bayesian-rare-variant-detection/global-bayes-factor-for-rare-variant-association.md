# Global Bayes factor for rare-variant association

**Model.** In a region with $p$ variants, $n$ subjects have genotypes $x_{ij}\in\{0,1,2\}$ (minor-allele counts), covariates $z_i$ and disease status $y_i\in\{0,1\}$. For a subset $\gamma$ of variants, model $M_\gamma$ is the logistic regression

$$\operatorname{logit}\mathbb{P}(y_i = 1) = \alpha_0 + z_i^{\top}\alpha + x_{i,\gamma}^{\top}\beta_\gamma .$$

The global test is $H_0: \gamma = \varnothing$ (no variant associated) against $H_1: \gamma \ne \varnothing$.

**Identity.** With prior $\pi(\gamma \mid H_1)$ over non-empty subsets and priors on $(\alpha_0,\alpha,\beta_\gamma)$, the global Bayes factor is the prior-weighted average of the individual model Bayes factors against the null:

$$\mathrm{BF}(H_1 : H_0) = \frac{m(D \mid H_1)}{m(D \mid H_0)} = \sum_{\gamma \ne \varnothing} \pi(\gamma \mid H_1)\,\mathrm{BF}(M_\gamma : M_\varnothing),\qquad \mathrm{BF}(M_\gamma : M_\varnothing) = \frac{m(D\mid M_\gamma)}{m(D\mid M_\varnothing)},$$

where $m(D\mid\cdot)$ is the marginal likelihood (evidence). With prior probabilities $\pi_0$ and $\pi_1 = 1-\pi_0$ on the hypotheses,

$$\pi(H_1\mid D) = \frac{\pi_1\,\mathrm{BF}}{\pi_0 + \pi_1\,\mathrm{BF}}.$$

**Prior choices for consistency.** Each $\beta_j$ is Gaussian with a variance drawn from an inverse-gamma prior truncated to a bounded interval, which keeps the eigenvalues of the prior covariance bounded; each variant enters independently with a prior inclusion probability that decreases with its minor allele frequency, favoring rare variants and controlling the a priori model size as $p$ grows.

## Expansion

The identity follows by writing $m(D\mid H_1) = \sum_\gamma \pi(\gamma\mid H_1)\,m(D\mid M_\gamma)$ and dividing by $m(D\mid H_0) = m(D\mid M_\varnothing)$. The sum ranges over $2^p - 1$ models, so it is estimated by Monte Carlo. Summing over the distinct models visited by an ordinary MCMC run only gives a lower bound; stochastic approximation Monte Carlo, which partitions the alternative model space by energy and adaptively reweights the partitions, gives a consistent estimator of the global Bayes factor. Because the Bayes factor depends on the model prior, the free hyperparameter of the inclusion-probability prior is chosen to maximize the evidence for $H_1$ (a type-II maximum-likelihood prior). The source chooses the truncated variance prior and the frequency-dependent inclusion prior so that the posterior is consistent; those consistency results are not part of this page, whose identity holds for any priors.

## Sources

- Liang F, Xiong M. Bayesian detection of causal rare variants under posterior consistency. *PLoS ONE* 8(7):e69633 (2013), Eqs. 1-4 and the Methods sections on priors, Bayes factor estimation and rare variant detection. <https://doi.org/10.1371/journal.pone.0069633>. PMCID: PMC3724943.
