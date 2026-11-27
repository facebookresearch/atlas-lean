# Mean coalescence times in the finite island model are expected absorption times

Let $d \ge 2$ and $M > 0$, and let $X$ be the continuous-time Markov chain on the three pair states (same deme, different demes, coalesced) with the island-model transition rates $q(\text{same}, \text{coalesced}) = 1$, $q(\text{same}, \text{different}) = M$ and $q(\text{different}, \text{same}) = M/(d - 1)$, time measured in units of $2N$ generations. Let $T$ be the hitting time of the coalesced state. Then

$$E_{\text{same}}[T] = d, \qquad E_{\text{different}}[T] = d + \frac{d - 1}{M}.$$

The derivation combines existing statements. The exit rates of the two transient states are positive, and the closed-form function $h$ with $h(\text{same}) = d$, $h(\text{different}) = d + (d - 1)/M$ and $h(\text{coalesced}) = 0$ satisfies the first-step equation in jump-chain form; by minimality of the mean hitting time, $E_s[T] \le h(s) < \infty$ for every state $s$, so $T$ is integrable and the chain is absorbed almost surely. The mean hitting time itself satisfies the first-step equation, and multiplying by the exit rate turns it into the rate form, whose unique solution is $h$; hence $E_s[T] = h(s)$. In particular the mean coalescence time of two genes from one deme does not depend on the migration rate, which is the island-model case of Strobeck's (1987, Abstract) observation that the expected average number of pairwise differences in a sample from a single subpopulation is $4NT\mu$, independent of the migration rates, for a general class of structured models including the island and circular stepping-stone models. The invariance of a size-weighted mean within-deme coalescence time under general conservative migration is a separate, more general statement.

## Depends on

- [Transition rates of the two-lineage structured coalescent](../../../Biology/coalescent-theory/structured-coalescent/rate.md)
- [Exit rate of a structured-coalescent state](../../../Biology/coalescent-theory/structured-coalescent/exit-rate.md)
- [First-step analysis in jump-chain form](../../../Biology/coalescent-theory/structured-coalescent/mean-coalescence-time-eq-first-step.md)
- [Mean coalescence times in the finite island model](../../../Biology/coalescent-theory/structured-coalescent/first-step-equations-iff.md)
- [Closed-form mean coalescence times in the island model](../../../Biology/coalescent-theory/structured-coalescent/mean-coalescence-time.md)

## Proof depends on

- [Hitting time of a continuous-time Markov chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/ctmc-hitting-time.md)
- [Mean hitting time, first-step equation](../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/lintegral-ctmc-hitting-time.md)
- [Minimality of the mean hitting time](../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/lintegral-ctmc-hitting-time-le.md)

## Expansion

1. The three-state chain with the island-model rates, and positivity of the exit rates of the transient states for $d \ge 2$ and $M > 0$.
2. The upper bound $E_s[T] \le h(s)$ from minimality, and integrability of $T$.
3. The first-step equation for $E_s[T]$ and its identification with $h$ through uniqueness of the solution of the rate-form equations.
4. The corollary for Slatkin's $F_{ST}$, whose closed form is computed from these expectations.

## Sources

- Original result: C. Strobeck, Average number of nucleotide differences in a sample from a single subpopulation: a test for population subdivision, Genetics 117 (1987), 149–153. <https://doi.org/10.1093/genetics/117.1.149> Its abstract states the independence of the within-subpopulation mean from the migration rates; the island-model values follow the derivation above.
