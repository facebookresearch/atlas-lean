# First step of a level

For a computation DAG and natural numbers $p$ and $d$, let $s_e$
be the number of steps of level $e$ on $p$ processors: $\lceil L_e / p \rceil$ if $p \ge 1$ and
$0$ if $p = 0$, where $L_e$ is the number of tasks of depth $e$. The first step of level $d$ is
$\sum_{e < d} s_e$.
