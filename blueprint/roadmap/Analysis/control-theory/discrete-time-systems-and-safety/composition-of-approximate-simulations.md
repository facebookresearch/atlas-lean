# Composition of approximate simulations

Let $A$, $B$ and $C$ be discrete systems with a common input set $U$ and states in a common metric space. If $R_1$ is an
input-matched $\varepsilon_1$-approximate simulation of $A$ by $B$ and $R_2$ an input-matched $\varepsilon_2$-approximate simulation of $B$
by $C$, then the relational composite $R_2 \circ R_1 = \{(x, z) : \exists y,\ (x, y) \in R_1,\ (y, z) \in R_2\}$ is an input-matched
$(\varepsilon_1 + \varepsilon_2)$-approximate simulation of $A$ by $C$.

## Proof

If $(x, y) \in R_1$ and $(y, z) \in R_2$ then $d(x, z) \le d(x, y) + d(y, z) \le \varepsilon_1 + \varepsilon_2$, and for every input $u$ the
successors satisfy $(f_A(x, u), f_B(y, u)) \in R_1$ and $(f_B(y, u), f_C(z, u)) \in R_2$, so $(f_A(x, u), f_C(z, u)) \in R_2 \circ R_1$.

## Expansion

A good expansion adds a page for each pending prerequisite below.

- Statement prerequisite: input-matched ε-approximate simulation between discrete systems with states in a common metric space (item 1 of the approximate-simulation node).

## Depends on

- [epsilon-approximate simulation between metric discrete systems](epsilon-approximate-simulation-between-metric-discrete-syste.md)
- [Discrete-time dynamical system (input-driven state-update map)](discrete-time-dynamical-system.md)

## Sources

- A. Girard and G. J. Pappas, *Approximation metrics for discrete and continuous systems*, IEEE Trans. Automatic Control 52(5) (2007), 782–798. Background reference.
