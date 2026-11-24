# Neighbours never eat together under resource ordering

In the transition system of the
three dining philosophers under the resource-ordered protocol, with the atom $p_j$ holding when
philosopher $j$ eats, the initial state, in which everybody thinks, satisfies the CTL formula
$\mathrm{AG}\,\neg(p_i \wedge p_{i+1})$ for every philosopher $i \in \{0, 1, 2\}$, with indices
modulo $3$: in no state reachable from the initial state do philosophers $i$ and $i + 1$ both
eat.
