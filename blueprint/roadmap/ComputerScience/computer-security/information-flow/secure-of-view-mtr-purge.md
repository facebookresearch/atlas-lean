# Security from views of purged runs

Let $\rightsquigarrow$ be a relation on the domains of a
machine and $\sim_u$ output consistent equivalence relations on its states, one for each domain $u$.
If $\mathrm{run}(s_0, \alpha) \sim_u \mathrm{run}(s_0, \mathrm{purge}(\alpha, u))$ for every action
sequence $\alpha$ and domain $u$, where $s_0$ is the initial state, then the machine is secure for
$\rightsquigarrow$.

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, Lemma 1.
