# Arrays after $t$ rounds of pointer jumping for suffix sums

Given a partial successor
function $\mathrm{succ}$ on nodes $0, \dots, n-1$ and values $x_v$ in an additive monoid $M$,
the pair of arrays after $0$ rounds stores the pointers $\mathrm{succ}(v)$ and the sums $x_v$,
and the pair after $t + 1$ rounds is one round of pointer jumping on arrays applied to the pair
after $t$ rounds.
