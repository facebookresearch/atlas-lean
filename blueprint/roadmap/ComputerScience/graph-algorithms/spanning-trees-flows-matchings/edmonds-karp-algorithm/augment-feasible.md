# Augmentation within residual capacities preserves feasibility

Let $c$ be a
capacity matrix with natural-number entries on the vertices $\{0, \dots, n-1\}$, let $s$
and $t$ be vertices, and let $f$ be a flow that is feasible for $c$, $s$, $t$. Let
$P = (v_0, \dots, v_k)$ be a nonempty list of pairwise distinct vertices with $v_0 = s$ and
$v_k = t$, and let $a$ be an integer with $0 \le a$ and
$a \le c(v_i, v_{i+1}) - f(v_i, v_{i+1})$ for every $i < k$. Then the augmentation of $f$
along $P$ by $a$ is feasible for $c$, $s$, $t$.
