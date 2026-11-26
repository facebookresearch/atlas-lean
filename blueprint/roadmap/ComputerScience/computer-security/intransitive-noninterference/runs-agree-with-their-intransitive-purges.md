# Runs agree with their intransitive purges

Let $M$ be a view-partitioned system and $\rightsquigarrow$ a policy, with $\approx^C$ as in [weak step consistency](weak-step-consistency.md), and $\mathrm{sources}$ and $\mathrm{ipurge}$ as in
[sources and intransitive purge](intransitive-purge.md).

**Lemma.** If $M$ is weakly step consistent and locally respects $\rightsquigarrow$, then $s \approx^{\mathrm{sources}(\alpha, u)} t$ implies
$\mathrm{run}(s, \alpha) \sim_u \mathrm{run}(t, \mathrm{ipurge}(\alpha, u))$.

The proof is by induction on $\alpha$: when $\mathrm{dom}(a) \in \mathrm{sources}(a \circ \alpha, u)$ the action is kept and the [one-step lemma](one-step-preserves-agreement-on-sources.md)
applies; otherwise it is purged and [purged actions are invisible](purged-actions-are-invisible-to-the-sources.md).

## Depends on

- [Weak step consistency](weak-step-consistency.md)
- [Sources and intransitive purge](intransitive-purge.md)

## Proof depends on

- [One step preserves agreement on the sources](one-step-preserves-agreement-on-sources.md)
- [Purged actions are invisible to the sources](purged-actions-are-invisible-to-the-sources.md)

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, <http://www.csl.sri.com/papers/csl-92-2/csl-92-2.pdf>: Chapter 4, Lemma 5 and its proof.
