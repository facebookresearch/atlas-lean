# Purged actions are invisible to the sources

Let $M$ be a view-partitioned system and $\rightsquigarrow$ a policy, with $\approx^C$ as in [weak step consistency](weak-step-consistency.md), and $\mathrm{sources}$ and $\mathrm{ipurge}$ as in
[sources and intransitive purge](intransitive-purge.md).

**Lemma.** If $M$ locally respects $\rightsquigarrow$ and $\mathrm{dom}(a) \notin \mathrm{sources}(a \circ \alpha, u)$, then $s \approx^{\mathrm{sources}(\alpha, u)} \mathrm{step}(s, a)$.

Every $v \in \mathrm{sources}(\alpha, u)$ has $\mathrm{dom}(a) \not\rightsquigarrow v$, since otherwise $\mathrm{dom}(a)$ would be a source, and local respect gives $s \sim_v \mathrm{step}(s, a)$.

## Depends on

- [Weak step consistency](weak-step-consistency.md)
- [Sources and intransitive purge](intransitive-purge.md)

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, <http://www.csl.sri.com/papers/csl-92-2/csl-92-2.pdf>: Chapter 4, Lemma 4 and its proof.
