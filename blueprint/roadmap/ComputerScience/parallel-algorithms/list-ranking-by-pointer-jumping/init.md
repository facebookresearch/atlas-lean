# Initial state of pointer jumping for suffix sums

Given nodes $0, \dots, n-1$ with a
partial successor function $\mathrm{succ}$ and values $x_v$ in an additive monoid $M$, the
initial state gives each node $v$ the pointer $\mathrm{succ}(v)$ (undefined at the end of a
list) and the sum $x_v$.
