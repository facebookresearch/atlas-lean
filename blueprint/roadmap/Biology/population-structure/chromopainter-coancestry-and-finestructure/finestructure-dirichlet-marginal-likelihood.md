# Dirichlet marginal likelihood of a population partition

In the [fineSTRUCTURE likelihood](finestructure-coancestry-likelihood.md), give each row $\theta_{a\cdot} = (\theta_{a1}, \dots, \theta_{aK})$ of the donor matrix an independent Dirichlet prior with parameters $\beta_{a1}, \dots, \beta_{aK} > 0$ (with the coordinate $\theta_{aa}$ omitted when $n_a = 1$).

**Statement.** For a fixed partition $a$ of the individuals into $K$ populations, the donor matrix integrates out in closed form:

$$\int L(x \mid \theta, a)\, \pi(d\theta) = \prod_{a=1}^{K}\left[\frac{\Gamma\!\big(\sum_{b}\beta_{ab}\big)}{\prod_{b}\Gamma(\beta_{ab})}\cdot\frac{\prod_{b}\Gamma\!\big(\beta_{ab} + X_{ab}/c\big)}{\Gamma\!\big(\sum_{b}(\beta_{ab} + X_{ab}/c)\big)}\cdot\prod_{b}\big(n_b - \delta_{ab}\big)^{-X_{ab}/c}\right],$$

where $X_{ab}$ is the coancestry total from population $b$ into population $a$ and $c$ is the normalization constant. The posterior of each row is again Dirichlet, with parameters $\beta_{ab} + X_{ab}/c$.

Consequently the posterior probability of a partition depends only on $c$, the prior hyperparameters and the totals $X_{ab}$, which allows Markov chain Monte Carlo over partitions (merge, split and move proposals, with a Dirichlet-process prior on partitions) without sampling $\theta$.

## Depends on

- [fineSTRUCTURE likelihood of a coancestry matrix](finestructure-coancestry-likelihood.md)

## Proof depends on

- [The Dirichlet integral](../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/lintegral-dirichlet-density.md)
- [Dirichlet–multinomial conjugacy](../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/with-density-prod-pow-dirichlet-measure.md)

## Expansion

For each recipient population $a$ the likelihood factor is $\prod_b \theta_{ab}^{X_{ab}/c}$ times the constant $\prod_b (n_b - \delta_{ab})^{-X_{ab}/c}$. Against the Dirichlet density $\Gamma(\sum_b\beta_{ab})\prod_b\theta_{ab}^{\beta_{ab}-1}/\prod_b\Gamma(\beta_{ab})$ the integral over the simplex is the Dirichlet normalizing constant evaluated at $\beta_{ab} + X_{ab}/c$; the exponents need not be integers. In the paper the prior parameters combine a shared variance term, an excess of within-population copying and a uniform split of the remaining chunks, with gamma hyperpriors on these parameters.

## Sources

- D. J. Lawson, G. Hellenthal, S. Myers and D. Falush, "Inference of population structure using dense haplotype data", PLoS Genetics 8 (2012), e1002453, Results, Equations (1)–(2) and section "MCMC scheme for assigning individuals to populations", <https://doi.org/10.1371/journal.pgen.1002453> (PMC3266881).
