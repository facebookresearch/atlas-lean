# Head drop along each arc of a pipe-flow solution

Let $V$ and $E$ be finite sets of nodes and arcs, each arc $e$ running from its tail $t(e)$ to its
head $h(e)$, and let $r$ (resistances) and $q$ (arc flows) be real functions on $E$ and $d$ (nodal
net inflows) and $H$ (heads) real functions on $V$. If the
[pipe-flow equations](is-pipe-flow-equations.md) hold, then on every arc $e$ the head at the tail
minus the head at the head is $H_{t(e)} - H_{h(e)} = r_e q_e |q_e|$.
