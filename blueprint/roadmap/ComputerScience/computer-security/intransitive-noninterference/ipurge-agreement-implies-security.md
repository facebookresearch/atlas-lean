# Agreement with the intransitive purge implies security

Let $M$ be a view-partitioned system and $\rightsquigarrow$ a policy, with $\approx^C$ as in [weak step consistency](weak-step-consistency.md), and $\mathrm{sources}$ and $\mathrm{ipurge}$ as in
[sources and intransitive purge](intransitive-purge.md).

**Lemma.** If $M$ is output consistent and $\mathrm{do}(\alpha) \sim_u \mathrm{do}(\mathrm{ipurge}(\alpha, u))$ for every domain $u$ and action sequence $\alpha$, then $M$ is
[secure for $\rightsquigarrow$](security-for-intransitive-policies.md).

Taking $u = \mathrm{dom}(a)$ and applying output consistency gives $\mathrm{test}(\alpha, a) = \mathrm{test}(\mathrm{ipurge}(\alpha, \mathrm{dom}(a)), a)$.

## Depends on

- [Security for intransitive policies](security-for-intransitive-policies.md)
- [Weak step consistency](weak-step-consistency.md)

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, <http://www.csl.sri.com/papers/csl-92-2/csl-92-2.pdf>: Chapter 4, Lemma 2 and its proof.
