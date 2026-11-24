# Conditioning on an ascertainment event can correlate drift increments

Restricting to sites that satisfy an ascertainment event $S$ with $\mu(S) > 0$ replaces the measure $\mu$ by $\mu_S = \mu(\cdot \mid S)$. The
[model-free f-statistic identities](../patterson-s-f-statistics/f2.md) hold for every measure, so they remain valid under $\mu_S$. The second-moment structure of the [drift model](../patterson-s-f-statistics/drift-model.md), with
mean-zero increments and zero cross moments, need not survive. Take a root at frequency $r = \frac12$, an edge to $X$ and an edge from $X$ to a leaf $A$,
each one step of [neutral binomial drift](../patterson-s-f-statistics/neutral-wright-fisher-on-a-tree-realizes-the-dri.md) $p \mapsto \mathrm{Binomial}(3, p)/3$. Unconditionally $\mathbb E[(x - r)(a - x)] = 0$, but with $S = \{0 < a < 1\}$ (polymorphic in $A$),

$$\mu(S) = \tfrac12, \qquad \mathbb E_{\mu_S}\bigl[(x - r)(a - x)\bigr] = -\tfrac1{54} \ne 0 .$$

So the drift-model hypotheses can fail for ascertained sites, even though f-statistics are still defined and their algebraic identities still hold.

## Depends on

- [Admixture-graph drift model](../patterson-s-f-statistics/drift-model.md)
- [f2 statistic](../patterson-s-f-statistics/f2.md)

## Related topics

- [Neutral binomial drift on a tree realizes the drift model](../patterson-s-f-statistics/neutral-wright-fisher-on-a-tree-realizes-the-dri.md)

## Sources

- N. Patterson et al., "Ancient admixture in human history", Genetics 192 (2012), 1065–1093, <https://doi.org/10.1534/genetics.112.145037>, sections on ascertainment and Appendix C. The counterexample is computed above in exact arithmetic.
