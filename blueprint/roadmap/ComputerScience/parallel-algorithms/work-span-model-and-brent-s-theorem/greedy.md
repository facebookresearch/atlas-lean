# Greedy schedule

A schedule $S$ of a computation DAG on $p$ processors is greedy if, for
every step $t$ and every task that is ready at step $t$, exactly $p$ tasks run in step $t$: a step
leaves a ready task waiting only when all $p$ processors are busy.
