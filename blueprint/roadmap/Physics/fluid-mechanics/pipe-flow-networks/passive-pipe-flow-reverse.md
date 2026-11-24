# Reversing all arcs and flows preserves passivity

Let $V$ and $E$ be finite sets of nodes and arcs, each arc $e$ running from its tail $t(e)$ to its
head $h(e)$, and let $r$ (resistances) and $q$ (arc flows) be real functions on $E$ and $d$ (nodal
net inflows) and $H$ (heads) real functions on $V$. If $(r, q, d, H)$ is a
[passive pipe flow](is-passive-pipe-flow.md), then so is $(r, -q, d, H)$ on the network with every
arc reversed, tail and head exchanged.
