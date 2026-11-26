# Runs and purged runs from equivalent states

Let $\sim_u$ be equivalence relations on the
states of a machine, one for each domain $u$, that are step consistent and locally respect a
relation $\rightsquigarrow$ on domains. If $s \sim_u t$, then
$\mathrm{run}(s, \alpha) \sim_u \mathrm{run}(t, \mathrm{purge}(\alpha, u))$ for every action
sequence $\alpha$.

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, proof of Theorem 1, equation (2.1).
