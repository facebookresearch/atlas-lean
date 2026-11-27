# List-ranking rounds on arrays

For a successor function $\mathrm{succ}$ on the nodes
$0, \dots, n - 1$ and $t \ge 0$, the arrays after $t$ rounds are a pair of arrays (pointers and
distances) defined by recursion on $t$: after $0$ rounds they are the tabulation of the initial
state of $\mathrm{succ}$, and after $t + 1$ rounds they are one round on arrays applied to the
arrays after $t$ rounds.
