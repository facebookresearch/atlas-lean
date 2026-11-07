# Depths of an initial segment of tasks

For $k \le n$, the list of the depths of tasks
$0, \dots, k - 1$ of a computation DAG on $n$ tasks, computed in topological order: the empty
list for $k = 0$, and for $k + 1$ the list for $k$ followed by $1$ plus the largest entry of that
list at a predecessor of task $k$ (or $1$ if task $k$ has no predecessors).
