# Type-conditioned genealogical distance in the two-type Moran model

Consider the neutral Moran model with two types $K = \{0,1\}$ in the large-population (tree-valued Fleming–Viot) limit, with time scaled so that two lineages coalesce at rate $1$, mutation at total rate $B > 0$ with mutation to type $0$ at rate $Bb_0 > 0$ and to type $1$ at rate $Bb_1 > 0$ ($b_0 + b_1 = 1$), and no selection. Sample two individuals from the stationary population and let $f_t(\circ)$, $f_t(\bullet)$, $f_t(\circ\bullet)$ be the conditional probabilities that their genealogical distance exceeds $2t$ given that both have type $0$, both have type $1$, or they have different types.

**Theorem.** For all $t \ge 0$,

$$
f_t(\circ) = e^{-t}\Big(1 + \frac{b_1(e^{-2Bt} - 1)}{1 + 2Bb_0}\Big), \qquad f_t(\bullet) = e^{-t}\Big(1 + \frac{b_0(e^{-2Bt} - 1)}{1 + 2Bb_1}\Big),
$$

$$
f_t(\circ\bullet) = e^{-t}\Big(1 - \frac{e^{-2Bt} - 1}{2B}\Big).
$$

Consequently:

1. the unconditioned half-distance is exponential with mean $1$;
2. $f_t(\circ) < f_t(\bullet)$ for all $t > 0$ if and only if $b_1 > b_0$;
3. $\max\{f_t(\circ), f_t(\bullet)\} < e^{-t} < f_t(\circ\bullet)$ for all $t > 0$: sharing a type makes individuals more closely related, different types less;
4. all three conditional laws tend to the exponential law $e^{-t}$ as $B \to \infty$.

With selection $S > 0$ the same strict ordering holds for small $t$, and the unconditioned tail $p_t$ satisfies $p_t < e^{-t}$ for small $t > 0$, with $\partial_t^3 p_t|_{t=0} = -(1 + 2S^2\,\mathbb{E}[1,0])$, where $\mathbb{E}[1,0]$ is the stationary probability that two sampled individuals have types $1$ and $0$.

## Expansion

The historical Moran model records, for each individual, its type and its whole ancestral line. A Feynman–Kac duality with a historical backward process, an $h$-transform of two coalescing lineages that also carry types backwards in time, turns type-conditioned genealogical questions into hitting problems of a small Markov jump process. For two lineages the backward chain on the states {both type 0, both type 1, different} is explicit, yielding the closed forms above. Mixing the three conditional laws with the stationary type frequencies recovers the Kingman exponential law.

## Sources

- Peter Seidel, *The historical Moran model*, arXiv:1511.05781, Section 3, propositions "Conditioned genealogical distance" and "Genealogical distance of two individuals", and Theorem 6 (Section 4). <https://doi.org/10.48550/arXiv.1511.05781>
