# One step preserves agreement on the sources

Let $M$ be a view-partitioned system and $\rightsquigarrow$ a policy, with $\approx^C$ as in [weak step consistency](weak-step-consistency.md), and $\mathrm{sources}$ and $\mathrm{ipurge}$ as in
[sources and intransitive purge](intransitive-purge.md).

**Lemma.** If $M$ is weakly step consistent and locally respects $\rightsquigarrow$, then $s \approx^{\mathrm{sources}(a \circ \alpha, u)} t$ implies
$\mathrm{step}(s, a) \approx^{\mathrm{sources}(\alpha, u)} \mathrm{step}(t, a)$.

For $v \in \mathrm{sources}(\alpha, u)$: if $\mathrm{dom}(a) \rightsquigarrow v$ then $\mathrm{dom}(a) \in \mathrm{sources}(a \circ \alpha, u)$ and weak step consistency applies; otherwise local
respect gives $\mathrm{step}(s, a) \sim_v s \sim_v t \sim_v \mathrm{step}(t, a)$.

## Depends on

- [Weak step consistency](weak-step-consistency.md)
- [Sources and intransitive purge](intransitive-purge.md)

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, <http://www.csl.sri.com/papers/csl-92-2/csl-92-2.pdf>: Chapter 4, Definitions 9–10, Lemma 3 and its proof.
