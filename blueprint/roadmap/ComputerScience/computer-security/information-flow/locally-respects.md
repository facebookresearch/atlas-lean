# Local respect of a policy

A family of equivalence relations $\sim_u$ on states, one for
each domain $u$ (`view u`), locally respects a relation $\rightsquigarrow$ on domains (`policy`)
if $\mathrm{dom}(a) \not\rightsquigarrow u$ implies $s \sim_u \mathrm{step}(s, a)$ for all
domains $u$, actions $a$ and states $s$.

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, Definition 4.
