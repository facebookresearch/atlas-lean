# Security for intransitive policies

Let $M$ be a system with states, initial state $s_0$, actions $A$, outputs, transition function $\mathrm{step}$, output function $\mathrm{output}(s, a)$ and domains
$\mathrm{dom}(a)$, as in the [unwinding theorem for noninterference](../information-flow/unwinding-theorem-for-noninterference.md), and write $\mathrm{do}(\alpha) = \mathrm{run}(s_0, \alpha)$ and
$\mathrm{test}(\alpha, a) = \mathrm{output}(\mathrm{do}(\alpha), a)$. Let $\rightsquigarrow$ be a reflexive, possibly intransitive, policy on domains. $M$ is *secure for* $\rightsquigarrow$
in the intransitive sense of Haigh and Young, as reformulated by Rushby, if
$$\mathrm{test}(\alpha, a) = \mathrm{test}(\mathrm{ipurge}(\alpha, \mathrm{dom}(a)), a)$$
for every action sequence $\alpha$ and action $a$, with $\mathrm{ipurge}$ the [intransitive purge](intransitive-purge.md). For a transitive policy this is the purge-based
notion of security.

## Depends on

- [Unwinding theorem for noninterference](../information-flow/unwinding-theorem-for-noninterference.md)
- [Sources and intransitive purge](intransitive-purge.md)

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, <http://www.csl.sri.com/papers/csl-92-2/csl-92-2.pdf>: Chapter 4, the definition of security for intransitive policies following Definition 8.
