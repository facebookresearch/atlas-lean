# Reversing all arcs and flows preserves the pipe-flow equations

Let $V$ and $E$ be finite sets of nodes and arcs, each arc $e$ running from its tail $t(e)$ to its
head $h(e)$, and let $r$ (resistances) and $q$ (arc flows) be real functions on $E$ and $d$ (nodal
net inflows) and $H$ (heads) real functions on $V$. If $(r, q, d, H)$ satisfies the
[pipe-flow equations](is-pipe-flow-equations.md), then so does $(r, -q, d, H)$ on the network with
every arc reversed, tail and head exchanged, with the same resistances, nodal net inflows and heads.
