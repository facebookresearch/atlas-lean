# Expected epoch lengths and first-coalescence means

Under a coalescent with variable population size, for a sample of $n \ge 2$ lineages let $\varphi_{n,k} = E[T_{n,k}]$ be the expected time during which exactly $k$ lineages remain ($2 \le k \le n$), let $\gamma_{n,b}$ be the expected total length of branches subtending $b$ leaves ($1 \le b \le n - 1$), and for $2 \le m \le n$ let $c_m = E[T_{m,m}]$ be the expected time to the first coalescence in a sample of $m$ lineages, and assume that each $T_{m,m}$ is integrable, $c_m = E[T_{m,m}] < \infty$ for $2 \le m \le n$, so that $\sum_k\gamma_{n,k}$ is finite and positive. This can fail even when coalescence is almost sure: if two lineages coalesce at rate $1/(1 + t)$, then $P(T_{2,2} > t) = 1/(1 + t)$ and $c_2 = \infty$. Then $\gamma_{n,b} = \sum_{k=2}^{n-b+1} k\binom{n-b-1}{k-2}\binom{n-1}{k-1}^{-1}\varphi_{n,k}$ (Griffiths and Tavaré 1998), the tail sums $\psi_{n,k} = \sum_{j \ge k}\varphi_{n,j}$ satisfy $\psi_{n,k} = \sum_{m=k}^n a_{km}c_m$ with $a_{km} = \prod_{l=k, l \ne m}^n\binom l2 \big/ \prod_{l=k, l \ne m}^n\bigl[\binom l2 - \binom m2\bigr]$, an invertible upper-triangular system (Polanski, Bobrowski and Kimmel 2003; Bhaskar and Song 2014, eqs. (7) and (8)). The consequence that the normalized expected spectrum $\xi_{n,b} = \gamma_{n,b}/\sum_k\gamma_{n,k}$ determines $(c_2, \dots, c_n)$ up to a common positive factor is Lemma 1 of [generalized Descartes rule and sign-change complexity of population size families](../../site-frequency-spectrum-under-variable-populatio/sign-change-complexity-and-demographic-identifiability/generalized-descartes-rule-and-sign-change-complexity.md) and is not restated here. The [expected spectrum under a variable size](../../site-frequency-spectrum-under-variable-populatio/variable-sfs.md) is the one parametrization and the first-coalescence means, from which piecewise histories are identifiable, are the other; the target is the explicit bridge between the two parametrizations: the two triangular relations above, their invertibility, and the multiplicative constant made explicit.

## Depends on

- [Expected site frequency spectrum under variable population size](../../site-frequency-spectrum-under-variable-populatio/variable-sfs.md)
- [Expected time to the first coalescence](../../site-frequency-spectrum-under-variable-populatio/first-coal-mean.md)

## Proof depends on

- [The expected SFS determines the mean holding times](../../site-frequency-spectrum-under-variable-populatio/eq-of-variable-sfs-eq.md)

## Expansion

1. The expected epoch lengths $E[T_{n,k}]$ and the [first-coalescence means](../../site-frequency-spectrum-under-variable-populatio/first-coal-mean.md) $c_m$ in a variable-size coalescent.
2. The relation $\gamma = M\varphi$ between branch lengths and epoch lengths, with $M$ upper-left triangular with positive anti-diagonal, hence invertible.
3. The relation $\psi = Ac$ between tail sums of epoch lengths and first-coalescence means, with $A$ upper triangular with nonzero diagonal, hence invertible.
4. If mutations occur at a known rate $\theta/2 > 0$ per unit of the time scale in which $T_{m,m}$ and $c_m$ are measured, the absolute expected counts $\frac{\theta}{2}\gamma_{n,b}$ of segregating sites subtending $b$ leaves determine $(c_2, \dots, c_n)$ exactly, by inverting the two triangular systems; the normalized spectrum $\xi_{n,b}$ alone does not, even with $\theta$ known.

## Sources

- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493. <https://arxiv.org/abs/1309.5056>
- Original result: R. C. Griffiths and S. Tavaré, The age of a mutation in a general coalescent tree, Comm. Statist. Stochastic Models 14 (1998), 273–295. <https://doi.org/10.1080/15326349808807471> The formula follows Bhaskar and Song (2014), eq. (7).
- Original result: A. Polanski, A. Bobrowski and M. Kimmel, A note on distributions of times to coalescence, under time-dependent population size, Theor. Popul. Biol. 63 (2003), 33–40. <https://doi.org/10.1016/s0040-5809(02)00010-2> The formula follows Bhaskar and Song (2014), eq. (8).
