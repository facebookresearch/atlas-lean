# Passive pipe flow: pipe-flow equations with nonnegative resistances

Let $V$ and $E$ be finite sets of nodes and arcs, each arc $e$ running from its tail $t(e)$ to its
head $h(e)$, and let $r$ (resistances) and $q$ (arc flows) be real functions on $E$ and $d$ (nodal
net inflows) and $H$ (heads) real functions on $V$. The data form a passive pipe flow when they
satisfy the [pipe-flow equations](is-pipe-flow-equations.md) and $r_e \geq 0$ for every arc $e$.
Nonnegative resistances model dissipative pipes; a negative resistance would model an active
element.
