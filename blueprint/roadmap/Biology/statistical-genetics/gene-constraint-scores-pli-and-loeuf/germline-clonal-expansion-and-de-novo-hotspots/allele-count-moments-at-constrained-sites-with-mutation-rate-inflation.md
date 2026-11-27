# Allele-count moments at constrained sites with mutation-rate inflation

**Setting.** Consider a class of strongly deleterious sites (for example loss-of-function sites in a gene) in a population of effective size $N_e$, each with per-generation mutation rate $\mu$ drawn from a distribution with mean $\mathbb E(\mu)$ and variance $\operatorname{Var}(\mu)$, and heterozygous selection coefficient $s$. Under the gamma approximation to mutation–selection–drift balance, the allele frequency $x$ at a site has a gamma distribution with shape $4N_e\mu$ and scale $1/(4N_e s)$. In a sample of $n$ chromosomes, the allele count $k$ satisfies $k \mid x \sim \mathrm{Poisson}(nx)$.

**Proposition.**

$$\mathbb E(k) = \frac{n\,\mathbb E(\mu)}{s},\qquad \operatorname{Var}(k) = \underbrace{\frac{n\,\mathbb E(\mu)}{s}}_{\text{sampling}} + \underbrace{\frac{n\,\mathbb E(\mu)}{s}\cdot\frac{n}{4N_e s}}_{\text{segregation}} + \underbrace{\frac{n^2}{s^2}\operatorname{Var}(\mu)}_{\text{rate heterogeneity}} .$$

**Corollary (clonal expansion).** If clonal expansion in the germline multiplies the effective mutation rate by a factor $\kappa \ge 1$, then

$$\mathbb E(k) = \kappa\,\frac{n\,\mathbb E(\mu)}{s},\qquad \operatorname{Var}(k) = \kappa\,\frac{n\,\mathbb E(\mu)}{s}\Big(1+\frac{n}{4N_e s}\Big) + \kappa^2\,\frac{n^2}{s^2}\operatorname{Var}(\mu).$$

Thus population allele counts at constrained sites scale linearly in $\kappa$ in the mean, and comparing observed counts with the rate-model expectation estimates the expansion factor.

## Depends on

- [Mean PTV count at mutation-selection balance](../../posterior-of-the-heterozygous-selection-coeffici/balance-mean.md): the mean count $n\mu/s$
- [Marginal mass of a Poisson mixture](../../../../Probability/bayesian-statistics/empirical-bayes-and-tweedie-s-formula/poisson-mixture-mass.md): the Poisson–gamma sampling model

## Proof depends on

- [Mean of the gamma law](../../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/integral-id-gamma-measure.md)
- [Variance of the gamma law](../../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/variance-id-gamma-measure.md)
- [Mean of the Poisson distribution](../../../population-genetics/haldane-s-survival-probability-of-a-beneficial-m/mean-poisson-measure.md)
- [Total variance splits into true-score and error variance](../../../../Probability/statistical-estimation/item-response-models/reliability-and-generalizability/variance-eq-variance-cond-exp-add-varian.md): the law of total variance

## Expansion

A gamma variable with shape $4N_e\mu$ and scale $1/(4N_e s)$ has mean $\mu/s$ (the deterministic mutation–selection equilibrium) and variance $\mu/(4N_e s^2)$ (drift around it). For fixed $\mu$, the Poisson–gamma mixture gives $\mathbb E(k\mid\mu) = n\mu/s$ and $\operatorname{Var}(k\mid\mu) = n\mu/s + n^2\mu/(4N_e s^2)$. The law of total variance then gives $\operatorname{Var}(k) = \mathbb E_\mu[\operatorname{Var}(k\mid\mu)] + \operatorname{Var}_\mu[\mathbb E(k\mid\mu)]$, which is the sum of the three displayed terms. Replacing $\mu$ by $\kappa\mu$ multiplies the first two terms by $\kappa$ and the third by $\kappa^2$. The rate-heterogeneity term can be estimated from the residual dispersion of the mutation-rate model, separating CES-driven excess from ordinary rate variation among sites. The same study reports that CES raises the average mutation rate of candidate loss-of-function driver genes roughly $17$-fold.

## Sources

- V. Seplyarskiy, M. A. Moldovan, E. Koch, P. Kar, M. D. C. Neville, R. Rahbari and S. Sunyaev, "Hotspots of human mutation point to clonal expansions in spermatogonia", Nature (2025), Methods, Eqs. (7)–(9), <https://doi.org/10.1038/s41586-025-09579-7>, PMCID PMC12714578.
