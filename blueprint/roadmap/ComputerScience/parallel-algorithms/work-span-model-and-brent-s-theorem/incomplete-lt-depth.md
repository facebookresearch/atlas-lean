# Each incomplete step advances the critical path

Let $S$ be a greedy schedule of a computation DAG on $p$ processors, with steps numbered from
$0$. For every task $v$, if $S$ runs $v$ in step $t$, then the number of incomplete steps before
step $t$ (steps $s < t$ in which fewer than $p$ tasks run) is strictly less than the depth of $v$.
