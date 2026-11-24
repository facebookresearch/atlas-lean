# Without negative cycles, Floyd–Warshall finds no negative diagonal entry

Let $w$
assign a weight in $\mathbb{Z} \cup \{\infty\}$ to each ordered pair of vertices in
$\{0, \dots, n-1\}$, and let $D$ be the distance matrix computed by Floyd–Warshall from $w$. If $w$
has no negative cycle, then the negative-diagonal check on $D$ returns false, that is,
$D(v, v) \ge 0$ for every vertex $v$.
