# Negative cycles

For an $n \times n$ matrix $w$ of weights in $\mathbb{Z} \cup \{+\infty\}$,
a list of vertices $v_0, \dots, v_m$ is a negative cycle when $m \ge 1$, $v_m = v_0$, every
weight $w_{v_i v_{i+1}}$ with $i < m$ is finite, the vertices $v_0, \dots, v_{m-1}$ are
pairwise distinct, and the path weight $\sum_{i < m} w_{v_i v_{i+1}}$ is negative.
