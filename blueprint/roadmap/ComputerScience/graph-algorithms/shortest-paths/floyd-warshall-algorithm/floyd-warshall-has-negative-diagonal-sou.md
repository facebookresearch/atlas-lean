# A negative diagonal entry in Floyd–Warshall reveals a negative cycle

Let $w$ assign a
weight in $\mathbb{Z} \cup \{\infty\}$ to each ordered pair of vertices in $\{0, \dots, n-1\}$, and
let $D$ be the distance matrix computed by Floyd–Warshall from $w$. If $D(v, v) < 0$ for some vertex
$v$, then $w$ has a negative cycle: a vertex sequence $v_0, v_1, \dots, v_m$ with $m \ge 1$ and
$v_m = v_0$, whose vertices $v_0, \dots, v_{m-1}$ are pairwise distinct, in which every consecutive
pair has finite weight, and whose total weight is negative.
