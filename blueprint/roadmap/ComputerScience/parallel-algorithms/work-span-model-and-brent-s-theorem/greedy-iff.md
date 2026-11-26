# Greediness need only be checked at the steps of the schedule

Let $S$ be a schedule of a
computation DAG on $p$ processors taking $T$ steps. Then $S$ is greedy if and only if, for every
step $t < T$ and every task $v$ that is ready at step $t$, exactly $p$ tasks run in step $t$.

This holds because a task is never ready at or after the last step.
