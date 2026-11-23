# State after $t$ rounds of pointer jumping for suffix sums

Given a partial successor
function $\mathrm{succ}$ on nodes $0, \dots, n-1$, values $x_v$ in an additive monoid $M$ and
$t \in \mathbb{N}$, the state after $t$ rounds is obtained from the initial state (pointers
$\mathrm{succ}(v)$, sums $x_v$) by applying one round of pointer jumping $t$ times.
