# Pairwise coalescence time under a variable population size

With relative size $\eta$ and clock $R(t) = \int_0^t \eta(s)^{-1}\, ds$ as in the variable-size coalescent, the coalescence time $T_2$ of two lineages satisfies $P(T_2 > t) = e^{-R(t)}$ for all $t \ge 0$. Consequently: $P(T_2 = \infty) = e^{-R(\infty)}$, which is positive exactly when $R(\infty) < \infty$; on $\{T_2 < \infty\}$, $T_2$ has density $\eta(t)^{-1}e^{-R(t)}$ (for almost every $t$) and hazard rate $1/\eta(t)$; and $E[T_2] = \int_0^\infty e^{-R(t)}\, dt$, finite or infinite (Griffiths and Tavaré 1994; Bhaskar and Song 2014, where the pair coalescence rate is $1/\eta(t)$ and eq. (1) gives the density of the first coalescence).

## Proof depends on

- [Survival-integral form of the first-coalescence quantity $c_m$](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/first-coal-mean-eq-integral.md)

## Expansion

1. The survival function from the time change of an $\mathrm{Exp}(1)$ variable: $T_2 = R^{-1}(E)$ with $E \sim \mathrm{Exp}(1)$.
2. Mass at infinity when $R(\infty) < \infty$.
3. The density and hazard, by absolute continuity of $R$ (Lebesgue differentiation of $\int 1/\eta$).
4. The expectation by the layer-cake formula; the [first-coalescence quantity in survival-integral form](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/first-coal-mean-eq-integral.md) for $m = 2$.

## Sources

- Original result: R. C. Griffiths and S. Tavaré, Sampling theory for neutral alleles in a varying environment, Philos. Trans. R. Soc. Lond. B 344 (1994), 403–410. <https://doi.org/10.1098/rstb.1994.0079> The statement follows Bhaskar and Song (2014), eq. (1) with $m = 2$.
- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493, eqs. (1) and (3). <https://arxiv.org/abs/1309.5056>
