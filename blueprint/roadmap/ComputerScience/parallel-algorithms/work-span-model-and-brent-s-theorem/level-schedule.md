# Brent's level schedule

Let $G$ be a computation DAG and $p \ge 1$. For each $d$ let
$L_d$ be the number of tasks of depth $d$ and $o_d = \sum_{e < d} \lceil L_e / p \rceil$, and for
each task $v$ let $r(v)$ be the number of tasks of the same depth as $v$ with a smaller number.
Brent's level schedule is the schedule of $G$ on $p$ processors that runs each task $v$ at step
$o_{\operatorname{depth}(v)} + \lfloor r(v) / p \rfloor$.

It runs the tasks level by level, in order of depth, each level of $L_d$ tasks in
$\lceil L_d / p \rceil$ steps of at most $p$ tasks.
