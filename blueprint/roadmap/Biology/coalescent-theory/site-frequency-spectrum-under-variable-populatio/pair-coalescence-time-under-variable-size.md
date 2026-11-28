# Mass at infinity, density and mean of the pairwise coalescence time under a variable population size

With relative size $\eta$ and clock $R(t) = \int_0^t \eta(s)^{-1}\, ds$, the [cumulative coalescence intensity](cum-rate.md) $R_\eta$, as in the variable-size coalescent (the linked inverse-instantaneous-coalescence-rate page writes $R$ for the survival function instead; here $R$ is the clock and the survival function is $e^{-R}$), the coalescence time $T_2$ of two lineages satisfies $P(T_2 > t) = e^{-R(t)}$ for all $t \ge 0$, and where it has a density its hazard rate is $1/\eta(t)$, so that its [inverse instantaneous coalescence rate](../inverse-instantaneous-coalescence-rate/iicr-of-a-pairwise-coalescence-time.md) is $\eta$ (the panmixia proposition there). Allowing $R(\infty) < \infty$: $P(T_2 = \infty) = e^{-R(\infty)}$, which is positive exactly when $R(\infty) < \infty$; $T_2$ has the subprobability density $f(t) = \eta(t)^{-1}e^{-R(t)}$ on $[0, \infty)$ (for almost every $t$), whose total mass is $P(T_2 < \infty) = 1 - e^{-R(\infty)}$; when $R(\infty) < \infty$, the law of $T_2$ conditional on $\{T_2 < \infty\}$ has the probability density $f(t)/(1 - e^{-R(\infty)})$ and hazard rate $f(t)/(e^{-R(t)} - e^{-R(\infty)})$; and $E[T_2] = \int_0^\infty e^{-R(t)}\, dt$, finite or infinite (Griffiths and Tavaré 1994; Bhaskar and Song 2014, where the pair coalescence rate is $1/\eta(t)$ and eq. (1) gives the density of the first coalescence).

## Depends on

- [Inverse instantaneous coalescence rate of a pairwise coalescence time](../inverse-instantaneous-coalescence-rate/iicr-of-a-pairwise-coalescence-time.md)
- [Cumulative coalescence intensity](cum-rate.md)

## Proof depends on

- [Survival-integral form of the first-coalescence quantity $c_m$](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/first-coal-mean-eq-integral.md)

## Expansion

1. The survival function from the time change of an $\mathrm{Exp}(1)$ variable: $T_2 = R^{-1}(E)$ with $E \sim \mathrm{Exp}(1)$, where $R^{-1}(e) = \inf\{t : R(t) \ge e\}$ is the generalized inverse with $\inf \emptyset = \infty$, so that $T_2 = \infty$ when $E \ge R(\infty)$.
2. Mass at infinity when $R(\infty) < \infty$.
3. The subprobability density and the conditional law, by absolute continuity of $R$ (Lebesgue differentiation of $\int 1/\eta$).
4. The expectation by the layer-cake formula; the [first-coalescence quantity in survival-integral form](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/first-coal-mean-eq-integral.md) for $m = 2$.

## Sources

- Original result: R. C. Griffiths and S. Tavaré, Sampling theory for neutral alleles in a varying environment, Philos. Trans. R. Soc. Lond. B 344 (1994), 403–410. <https://doi.org/10.1098/rstb.1994.0079> The statement follows Bhaskar and Song (2014), eq. (1) with $m = 2$.
- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493, eqs. (1) and (3). <https://arxiv.org/abs/1309.5056>
