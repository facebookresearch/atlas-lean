# Preferential sampling and the serial-sampling likelihood

Coalescent likelihoods for serially sampled sequences usually condition on the sampling times, implicitly assuming that they are fixed by the sampling protocol or that their distribution does not depend on the population size. Karcher et al. (2016) model preferential sampling by taking the sampling times as an inhomogeneous Poisson process on a fixed window $[0, s_0]$ with intensity $\lambda(t) = e^{\beta_0}N_\gamma(t)^{\beta_1}$, a power of the effective population size $N_\gamma$, which adds to the coalescent likelihood the sampling log-likelihood

$$\log \Pr(s \mid \gamma, \beta_0, \beta_1) = C + n\beta_0 + \sum_{i=1}^n \beta_1 \log N_\gamma(s_i) - \int_{s_m}^{s_0} e^{\beta_0} N_\gamma(r)^{\beta_1}\, dr;$$

$\beta_1 = 0$ gives sampling times independent of $N_\gamma$ and $\beta_1 = 1$ an intensity proportional to it. Their simulations show that when sampling times depend on the effective population size, methods that condition on them without this term can be systematically biased, and that including it reduces bias and improves precision. The coalescent factor itself is unchanged: the genealogy depends on the sampling times, so it is conditioned on $s$, and $s$ contributes its own Poisson likelihood.

## Depends on

- [Heterochronous Λ-coalescent likelihood with variable effective population size](../../multiple-merger-coalescents/multiple-merger-coalescent-inference-of-effective-population-size/heterochronous-lambda-coalescent-likelihood-with-variable-effective-population-size.md)

## Expansion

1. The conditional density of a genealogy given fixed sampling times.
2. The inhomogeneous Poisson sampling model with intensity $e^{\beta_0}N(t)^{\beta_1}$ and its likelihood on the sampling window.
3. The joint density of genealogy and sampling times as the product of the two factors, and the posterior under priors on $\beta_0$, $\beta_1$ and $N$.
4. An explicit history and sampling intensity for which the estimate of $N$ that ignores the sampling factor differs in expectation from the estimate that includes it.

## Sources

- M. D. Karcher, J. A. Palacios, T. Bedford, M. A. Suchard and V. N. Minin, Quantifying and mitigating the effect of preferential sampling on phylodynamic inference, PLoS Comput. Biol. 12 (2016), e1004789, abstract and Methods (sampling model and sampling log-likelihood). <https://doi.org/10.1371/journal.pcbi.1004789>
