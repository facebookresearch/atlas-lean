# Weak step consistency

Let $M$ be a view-partitioned system, with an equivalence relation $\sim_u$ on states for each domain $u$, as in the
[unwinding theorem for noninterference](../information-flow/unwinding-theorem-for-noninterference.md). For a set $C$ of domains, $s \approx^C t$ holds when $s \sim_u t$ for every $u \in C$. $M$ is *weakly step consistent*
if $s \sim_u t$ and $s \sim_{\mathrm{dom}(a)} t$ imply $\mathrm{step}(s, a) \sim_u \mathrm{step}(t, a)$, for all states $s, t$, domains $u$ and actions $a$. Step consistency, which drops the
hypothesis $s \sim_{\mathrm{dom}(a)} t$, implies weak step consistency.

## Depends on

- [Unwinding theorem for noninterference](../information-flow/unwinding-theorem-for-noninterference.md)

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, <http://www.csl.sri.com/papers/csl-92-2/csl-92-2.pdf>: Chapter 4, Definitions 9 and 10.
