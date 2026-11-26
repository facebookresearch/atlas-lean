# Unwinding theorem for intransitive policies

Let $M$ be a view-partitioned system, with an equivalence relation $\sim_u$ on states for each domain $u$, and $\rightsquigarrow$ a policy. $M$ is *weakly step consistent* if
$s \sim_u t$ and $s \sim_{\mathrm{dom}(a)} t$ imply $\mathrm{step}(s, a) \sim_u \mathrm{step}(t, a)$; output consistency ($s \sim_{\mathrm{dom}(a)} t$ implies
$\mathrm{output}(s, a) = \mathrm{output}(t, a)$) and local respect ($\mathrm{dom}(a) \not\rightsquigarrow u$ implies $s \sim_u \mathrm{step}(s, a)$) are as in the
[unwinding theorem for noninterference](../information-flow/unwinding-theorem-for-noninterference.md).

**Theorem (Rushby).** If $M$ is output consistent, weakly step consistent and locally respects $\rightsquigarrow$, then $M$ is
[secure for $\rightsquigarrow$ in the intransitive sense](security-for-intransitive-policies.md).

The proof shows $\mathrm{run}(s, \alpha) \sim_u \mathrm{run}(t, \mathrm{ipurge}(\alpha, u))$ whenever $s$ and $t$ agree for every domain in $\mathrm{sources}(\alpha, u)$, and
specializes it to $s = t = s_0$.

## Depends on

- [Security for intransitive policies](security-for-intransitive-policies.md)
- [Unwinding theorem for noninterference](../information-flow/unwinding-theorem-for-noninterference.md)

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, <http://www.csl.sri.com/papers/csl-92-2/csl-92-2.pdf>: Chapter 4, Definitions 9–10, Lemmas 2–5 and Theorem 7 (unwinding theorem for intransitive policies) with its proof.
