# First-coalescence means of the variable-size coalescent

In the variable-size coalescent with clock $R$, for a sample of $m \ge 2$ lineages the time $T_{m,m}$ until the first coalescence satisfies $P(T_{m,m} > t) = \exp(-\binom m2 R(t))$, since the $\binom m2$ pairs each coalesce at rate $1/\eta$ until the first event; hence the first-coalescence mean is
$$c_m = E[T_{m,m}] = \int_0^\infty \exp\Bigl(-\binom m2 R(t)\Bigr)\, dt$$
(Polanski and Kimmel 2003; Bhaskar and Song 2014, eq. (3), which obtains it by integration by parts when $E[T_{m,m}] < \infty$). This connects the analytic definition of $c_m$ to the genealogical process.

## Expansion

1. The first-coalescence time of $m$ lineages as $R^{-1}$ of an $\mathrm{Exp}(\binom m2)$ variable.
2. The survival function and the layer-cake formula for $c_m$.
3. The identity with the [expected time to the first coalescence](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/first-coal-mean.md) and its [survival-integral form](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/first-coal-mean-eq-integral.md).
4. Identifiability of piecewise-constant histories from $(c_2, \dots, c_n)$ ([Bhaskar–Song identifiability](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/size-fn-eq-of-first-coal-mean-eq.md)) as the downstream use.

## Sources

- Original result: A. Polanski and M. Kimmel, New explicit expressions for relative frequencies of single-nucleotide polymorphisms with application to statistical inference on population growth, Genetics 165 (2003), 427–436. <https://doi.org/10.1093/genetics/165.1.427> The formula follows Bhaskar and Song (2014), eq. (3).
- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493, eqs. (1) and (3). <https://arxiv.org/abs/1309.5056>
