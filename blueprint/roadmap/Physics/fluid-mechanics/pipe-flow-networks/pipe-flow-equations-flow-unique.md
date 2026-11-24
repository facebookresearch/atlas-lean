# With positive resistances and equal inflows the arc flows are unique

Let $V$ and $E$ be finite sets of nodes and arcs, each arc $e$ running from $t(e)$ to $h(e)$, and
let $r_e > 0$ for every arc. If $(q_1, H_1)$ and $(q_2, H_2)$ both satisfy the
[pipe-flow equations](is-pipe-flow-equations.md) with the resistances $r$ and the same nodal net
inflows $d$, then $q_1 = q_2$. No connectivity is assumed, and the heads need not agree; with a
connected network and one common head they do
([uniqueness with an anchored head](pipe-flow-equations-unique-of-anchor.md)).
