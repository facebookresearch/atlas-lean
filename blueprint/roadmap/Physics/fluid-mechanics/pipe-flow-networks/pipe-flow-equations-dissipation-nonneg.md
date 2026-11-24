# With nonnegative resistances the dissipation pairing is nonnegative

Let $V$ and $E$ be finite sets of nodes and arcs, each arc $e$ running from its tail $t(e)$ to its
head $h(e)$, and let $r$ (resistances) and $q$ (arc flows) be real functions on $E$ and $d$ (nodal
net inflows) and $H$ (heads) real functions on $V$. If the
[pipe-flow equations](is-pipe-flow-equations.md) hold and $r_e \geq 0$ for every arc, then
$-\sum_{i \in V} H_i d_i \geq 0$: the [dissipation](pipe-flow-equations-dissipation.md)
$\sum_e r_e q_e^2 |q_e|$ is nonnegative. Equivalently, the pairing is nonnegative for every
[passive pipe flow](is-passive-pipe-flow.md), which is exactly a solution of the pipe-flow equations
with $r_e \geq 0$ for every arc.
