# The no-sensitive-upgrade monitor enforces noninterference

**Theorem (Austin and Flanagan).** For the [no-sensitive-upgrade monitor](no-sensitive-upgrade-monitoring.md) with universal labelling, if $\sigma_1 \approx_H \sigma_2$, $\theta_1 \sim_H \theta_2$,
$\sigma_1, \theta_1, e \Downarrow_{pc} \sigma'_1, v_1$ and $\sigma_2, \theta_2, e \Downarrow_{pc} \sigma'_2, v_2$, then $\sigma'_1 \approx_H \sigma'_2$ and $v_1 \sim_H v_2$: two runs from stores and environments that
differ only in data labelled $H$ or higher end with results that differ only there. Runs that stop with an error are not covered, so the monitor is termination
insensitive and may leak one bit through its error.

The proof is by induction on the first derivation with case analysis on its last rule.

## Depends on

- [Dynamic information-flow monitoring with no sensitive upgrades](no-sensitive-upgrade-monitoring.md)

## Sources

- T. H. Austin and C. Flanagan, "Efficient purely-dynamic information flow analysis", *Proceedings of the ACM SIGPLAN Fourth Workshop on Programming Languages and Analysis for Security (PLAS 2009)*, pp. 113–124, copy at <https://users.soe.ucsc.edu/~cormac/papers/plas09.pdf>: Section 3.1, Theorem 1 (non-interference for universal labeling) and the discussion of the no-sensitive-upgrade check.
