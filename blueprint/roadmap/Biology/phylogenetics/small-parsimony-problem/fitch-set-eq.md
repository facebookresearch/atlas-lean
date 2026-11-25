# Fitch's root set is the set of optimal root states

For a finite state set, observed states $\sigma$ and a tree $t$ with [unit costs](is-unit-cost.md), the set returned by [Fitch's algorithm](fitch.md) is the set of states $s$ with $\mathrm{Sk}(t, s)$ equal to Fitch's count, where $\mathrm{Sk}$ is [Sankoff's cost](sankoff.md).

## Sources

- J. A. Hartigan, *Minimum mutation fits to a given tree*, Biometrics 29 (1973), 53–65.
