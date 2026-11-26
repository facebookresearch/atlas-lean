# Ascertainment bound on de novo mutation enrichment

**Setting.** A cohort of parent–offspring trios is ascertained because the offspring has a disease $D$ of population prevalence $P(D)$. For a site or set of sites, let $V$ be the event that a child carries a de novo mutation there, with population probability $P(V)$ given by a mutation-rate model calibrated on neutral (for example synonymous) de novo mutations. The expected number of de novo mutations in the cohort under the model is proportional to $P(V)$ and the observed number to $P(V\mid D)$.

**Proposition.** If the mutation rate at the sites is the same in the general population as assumed by the model, then

$$\frac{\text{observed}}{\text{expected}} \approx \frac{P(V\mid D)}{P(V)} = \frac{P(D\mid V)}{P(D)} \le \frac{1}{P(D)} .$$

Consequently, an enrichment ratio significantly above $1/P^{*}(D)$, where $P^{*}(D)$ is a lower bound on the prevalence of the ascertained phenotype, cannot be explained by disease causation alone and indicates that the effective mutation rate at those sites is inflated, as happens for drivers of clonal expansion in spermatogonia (CES).

**Test.** For a gene $g$ with model loss-of-function mutation rate $\lambda_g$ (expected count in the cohort), a one-sided Poisson test of the observed count against mean $\lambda_g/P^{*}(D)$ rejects the hypothesis that the gene is merely a fully penetrant disease gene with normal mutation rate.

## Depends on

- [Poisson likelihood of an observed count](../poisson-lik.md): the Poisson count model of the test

## Proof depends on

- [Bayes' rule for discrete observations](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/posterior-eq-bayes-posterior.md): $P(V \mid D)/P(V) = P(D \mid V)/P(D)$

## Expansion

The middle equality is Bayes' rule, and the bound uses $P(D\mid V) \le 1$: even if every carrier of the mutation is affected, the ascertained cohort can be enriched for carriers by at most the inverse prevalence. If clonal expansion multiplies the per-generation rate by $\kappa > 1$, the true $P(V)$ is $\kappa$ times the model value, so the ratio becomes $\kappa P(D\mid V)/P(D)$ and can exceed $1/P(D)$. The test is conservative only if the prevalence is not overestimated, so a deliberately low $P^{*}(D)$ is used, and it needs phenotypically homogeneous ascertainment across sub-cohorts; for single missense sites the bound is applied site by site with a multiple-testing correction, and for loss-of-function variants it is applied to all such sites in a gene pooled. Overdispersion of the mutation-rate model is checked by comparing Poisson and negative-binomial likelihoods of recurrent synonymous de novo counts.

## Sources

- V. Seplyarskiy, M. A. Moldovan, E. Koch, P. Kar, M. D. C. Neville, R. Rahbari and S. Sunyaev, "Hotspots of human mutation point to clonal expansions in spermatogonia", Nature (2025), main text Eq. (1) and Fig. 1b, and Methods (mutation-rate model Eqs. (2)–(4), "Construction of the LoF-1 set", "Prevalence of NDD"), <https://doi.org/10.1038/s41586-025-09579-7>, PMCID PMC12714578.
