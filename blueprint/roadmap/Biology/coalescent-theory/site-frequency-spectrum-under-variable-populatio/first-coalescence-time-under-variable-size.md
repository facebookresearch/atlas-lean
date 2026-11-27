# First-coalescence means of the variable-size coalescent

In the variable-size coalescent with positive relative size $\eta$, $1/\eta$ locally integrable, and clock $R$ (the [cumulative coalescence intensity](cum-rate.md) $R = R_\eta$), for a sample of $m \ge 2$ lineages the time $T_{m,m} \in [0, \infty]$ until the first coalescence, with $T_{m,m} = \infty$ if no coalescence ever occurs, satisfies $P(T_{m,m} > t) = \exp(-\binom m2 R(t))$ for all $t \ge 0$, since the $\binom m2$ pairs each coalesce at rate $1/\eta$ until the first event. Hence, by the layer-cake formula, in $[0, \infty]$,

$$E[T_{m,m}] = \int_0^\infty \exp\Bigl(-\binom m2 R(t)\Bigr)\, dt$$

(Polanski and Kimmel 2003; Bhaskar and Song 2014, eq. (3), which obtains it by integration by parts when $E[T_{m,m}] < \infty$). When this mean is finite, it equals the real first-coalescence quantity $c_m$ of the [linked definition](first-coal-mean.md), which connects the analytic definition of $c_m$ to the genealogical process. When it is infinite, the identification fails: for $\eta(t) = e^t$ and $m = 2$, $R(\infty) = 1$, no coalescence occurs with probability $e^{-1}$, the mean is infinite, and $c_2$ is $0$ only by the convention of that definition.

## Depends on

- [Expected time to the first coalescence](first-coal-mean.md)
- [Cumulative coalescence intensity](cum-rate.md)

## Proof depends on

- [Survival-integral form of the first-coalescence quantity $c_m$](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/first-coal-mean-eq-integral.md)

## Expansion

1. The first-coalescence time of $m$ lineages as $R^{-1}$ of an $\mathrm{Exp}(\binom m2)$ variable, with $R^{-1}(e) = \inf\{t : R(t) \ge e\}$ the generalized inverse and $\inf \emptyset = \infty$, so that the time is infinite when the draw is at least $R(\infty)$.
2. The survival function and the extended layer-cake identity for $E[T_{m,m}] \in [0, \infty]$.
3. When $E[T_{m,m}] < \infty$, the identity with the [expected time to the first coalescence](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/first-coal-mean.md) and its [survival-integral form](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/first-coal-mean-eq-integral.md).
4. Identifiability of piecewise-constant histories from $(c_2, \dots, c_n)$ ([Bhaskar–Song identifiability](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/size-fn-eq-of-first-coal-mean-eq.md)) as the downstream use.

## Sources

- Original result: A. Polanski and M. Kimmel, New explicit expressions for relative frequencies of single-nucleotide polymorphisms with application to statistical inference on population growth, Genetics 165 (2003), 427–436. <https://doi.org/10.1093/genetics/165.1.427> The formula follows Bhaskar and Song (2014), eq. (3).
- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493, eqs. (1) and (3). <https://arxiv.org/abs/1309.5056>
