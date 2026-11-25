# A consistent heuristic that vanishes at the goal is admissible

Let $G$ be a directed graph on the vertices $\{0, \dots, n-1\}$ with natural edge weights $w$, and
let $h$ be a [consistent](consistent.md) heuristic with natural values. If $h(t) = 0$ for a goal
vertex $t$, then $h$ is [admissible](admissible.md) for $t$: $h(v) \le d$ for every vertex $v$ and
every weight $d$ of a path in $G$ from $v$ to $t$.
