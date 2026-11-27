# The no-sensitive-upgrade monitor enforces noninterference

**Theorem (Austin and Flanagan).** For the [no-sensitive-upgrade monitor](no-sensitive-upgrade-monitoring.md) with universal labelling, if $\sigma_1 \approx_H \sigma_2$, $\theta_1 \sim_H \theta_2$,
$\sigma_1, \theta_1, e \Downarrow_{pc} \sigma'_1, v_1$ and $\sigma_2, \theta_2, e \Downarrow_{pc} \sigma'_2, v_2$, then $\sigma'_1 \approx_H \sigma'_2$ and $v_1 \sim_H v_2$, provided the two runs choose their fresh addresses consistently: corresponding allocations in the two runs pick the same
fresh address, and allocations made by only one run (under a program counter at least $H$) pick addresses fresh for both runs, as in the coupled allocations of the
source's proof. The statement makes no claim for allocations chosen independently in the two runs. In words: two runs from stores and environments that
differ only in data labelled $H$ or higher end with results that differ only there. Runs that stop with an error are not covered, so the monitor is termination
insensitive and may leak one bit through its error.

The proof is by induction on the first derivation with case analysis on its last rule.

## Depends on

- [Dynamic information-flow monitoring with no sensitive upgrades](no-sensitive-upgrade-monitoring.md)

## Sources

- T. H. Austin and C. Flanagan, "Efficient purely-dynamic information flow analysis", *Proceedings of the ACM SIGPLAN Fourth Workshop on Programming Languages and Analysis for Security (PLAS 2009)*, pp. 113–124, copy at <https://users.soe.ucsc.edu/~cormac/papers/plas09.pdf>: Section 3.1, Theorem 1 (non-interference for universal labeling) and the discussion of the no-sensitive-upgrade check, and the proofs in the appendix of the copy, which assume without loss of generality that corresponding allocations use the same address and that the two runs otherwise allocate from disjoint parts of the address space.
