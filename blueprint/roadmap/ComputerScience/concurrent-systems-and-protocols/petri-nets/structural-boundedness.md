# Structural boundedness of Petri nets

A pure [Petri net](place-transition-petri-nets.md) $N$ with $m$ places is *structurally bounded* if $(N, M_0)$ is [bounded](boundedness-and-safeness.md) for every finite initial marking $M_0$. With $A$ its incidence matrix (see [the state equation](state-equation.md)), $N$ is structurally bounded if and only if there is an $m$-vector $y$ of positive integers with $A y \le 0$.

## Depends on

- [The state equation of a Petri net](state-equation.md)
- [Boundedness and safeness of Petri nets](boundedness-and-safeness.md)
- [Place/transition Petri nets](place-transition-petri-nets.md)

## Proof depends on

- [Farkas certificates for linear rational arithmetic](../../../TheoryOfComputation/decision-procedures/satisfiability-modulo-theories/farkas-certificates-for-linear-rational.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section VIII: the definition of structural boundedness and Theorem 29.
