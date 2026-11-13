# Step of a task in Brent's schedule

Let $G$ be a computation DAG and $p$ a natural number.
If $p \ge 1$, for each $d$ let $L_d$ be the number of tasks of depth $d$ and
$o_d = \sum_{e < d} \lceil L_e / p \rceil$, and for each task $v$ let $r(v)$ be the number of tasks
of the same depth as $v$ with a smaller number; the step of a task $v$ is
$o_{\operatorname{depth}(v)} + \lfloor r(v) / p \rfloor$. If $p = 0$, the step of every task is $0$.

For $p \ge 1$ this runs the tasks level by level, each level of $L_d$ tasks in
$\lceil L_d / p \rceil$ steps of at most $p$ tasks.
