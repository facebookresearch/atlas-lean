# A greedy schedule never idles

Let $S$ be a greedy schedule of a task graph on $p$
processors that takes $T$ steps, numbered $0, \dots, T - 1$. Then every step $t < T$ of $S$
runs at least one task.

The task that runs earliest among those not run before step $t$ has all its predecessors done
before step $t$. If step $t$ ran no task, this task would be ready at step $t$, while a greedy
step with a ready task keeps all $p$ processors busy.
