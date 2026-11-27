# Stochasticity-heterogeneity decomposition of longevity variance

**Markov chain moments.** Let $\tilde U$ be the $\omega g \times \omega g$ substochastic transient matrix of an absorbing Markov chain over age × frailty states, with death absorbing; individuals age one class per step and keep their frailty class. The fundamental matrix $\tilde N = (I - \tilde U)^{-1}$ has $(i,j)$ entry equal to the expected number of visits to state $i$ by an individual starting in state $j$. The vectors of first and second moments and variance of longevity (remaining life measured in steps) from each starting state are

$$\tilde\eta_1 = \big(\mathbf 1^{\mathsf T}\tilde N\big)^{\mathsf T}, \qquad \tilde\eta_2 = \big[\tilde\eta_1^{\mathsf T}(2\tilde N - I)\big]^{\mathsf T}, \qquad V(\tilde\eta) = \tilde\eta_2 - \tilde\eta_1 \circ \tilde\eta_1.$$

For the $g$ frailty groups in age class 1, $E(\eta_{\text{groups}}) = (e_1^{\mathsf T} \otimes I_g)\tilde\eta_1$ and $V(\eta_{\text{groups}}) = (e_1^{\mathsf T} \otimes I_g)V(\tilde\eta)$.

**Decomposition.** If age-1 individuals are a mixture of frailty groups with mixing distribution $\pi$, the variance of longevity satisfies the law of total variance

$$V(\eta) = \underbrace{\pi^{\mathsf T} V(\eta_{\text{groups}})}_{V_{\text{within}}} + \underbrace{\pi^{\mathsf T}\big[E(\eta_{\text{groups}}) \circ E(\eta_{\text{groups}})\big] - \big[\pi^{\mathsf T} E(\eta_{\text{groups}})\big]^2}_{V_{\text{between}}},$$

where $V_{\text{within}}$ is the variance due to individual stochasticity (random survival outcomes among individuals with identical rates) and $V_{\text{between}}$ is the variance due to heterogeneity in frailty; the ratio $V_{\text{between}}/V(\eta)$ is the fraction of longevity variance explained by heterogeneity.

## Depends on

- [Gamma-Gompertz-Makeham frailty hazard](gamma-gompertz-makeham-frailty-hazard.md)
- [State distribution in a discrete-time multistate life table](../../life-tables/multistate-life-table-by-matrix-products.md)
- [Total-variance decomposition](../../../../Probability/not-yet-classified/part-05/finite-conditioning/sum-mul-sq-sub-eq-within-add-between.md)

## Expansion

The number of steps before absorption is the total number of visits to transient states, so its mean is the column sum of $\tilde N$, and the standard identity for the second moment of visit counts in an absorbing chain gives $\tilde\eta_2$. Decomposing over frailty groups is exactly the analysis-of-variance identity $V = E[V(\cdot\mid\text{group})] + V[E(\cdot\mid\text{group})]$, the same one behind heritability, and it needs no hypothetical removal of frailty. Applied to $\Gamma$GM fits for cohorts from Sweden (1751–1899), France (1816–1903) and Italy (1872–1899), heterogeneous frailty accounted for less than 10% of the variance in adult longevity for both sexes, so most variance in human lifespan arises from individual stochasticity.

## Sources

- N. Hartemink, T. I. Missov, H. Caswell, "Stochasticity, heterogeneity, and variance in longevity in human populations", Theoretical Population Biology 114:107–116 (2017), Section 3.2 (Eqs 14–25) and Section 6, <https://doi.org/10.1016/j.tpb.2017.01.001>, PMCID PMC5336383.
