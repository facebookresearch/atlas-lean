# Weight matrices without negative cycles

Let $w$ assign to each ordered pair of vertices
in $\{0, \dots, n-1\}$ a weight in $\mathbb{Z} \cup \{\infty\}$. Then $w$ has no negative cycle
when there is no list of vertices $v_0, v_1, \dots, v_m$ with $m \ge 1$ such that $v_m = v_0$,
the vertices $v_0, \dots, v_{m-1}$ are pairwise distinct, $w(v_{i-1}, v_i) \ne \infty$ for
$1 \le i \le m$, and $w(v_0, v_1) + \cdots + w(v_{m-1}, v_m) < 0$.
