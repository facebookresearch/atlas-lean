# S-invariants of a Petri net

Let $A$ be the incidence matrix of a pure [Petri net](place-transition-petri-nets.md) $N$ with $m$ places (see [the state equation](state-equation.md)). An integer $m$-vector $y$ is an *S-invariant* if $A y = 0$. Then $y$ is an S-invariant if and only if $M^T y = M_0^T y$ for every initial marking $M_0$ and every marking $M$ reachable from $M_0$: the $y$-weighted token count is preserved by every firing.

## Depends on

- [The state equation of a Petri net](state-equation.md)
- [Place/transition Petri nets](place-transition-petri-nets.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section VIII: the definition of S- and T-invariants and Theorem 33.
