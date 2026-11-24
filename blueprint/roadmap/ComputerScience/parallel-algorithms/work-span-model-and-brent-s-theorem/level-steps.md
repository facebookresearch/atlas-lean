# Steps of a level

For a computation DAG and natural numbers $p$ and $d$, let $L_d$ be the
number of tasks of depth $d$. The number of steps of level $d$ on $p$ processors is
$\lceil L_d / p \rceil$ if $p \ge 1$, and $0$ if $p = 0$.
