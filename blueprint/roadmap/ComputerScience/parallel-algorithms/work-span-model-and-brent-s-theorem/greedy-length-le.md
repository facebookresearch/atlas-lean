# The greedy scheduling bound

Let $G$ be a computation DAG with $n$ tasks and span $D$, and
let $S$ be a greedy schedule of $G$ on $p$ processors taking $T$ steps. Then
$pT \le n + (p - 1)D$.

Each complete step runs $p$ tasks, and each of the at most $D$ incomplete steps runs at least one.

## Sources

- R. L. Graham, "Bounds for certain multiprocessing anomalies", *Bell System Technical Journal* 45(9) (1966), 1563–1581: the unit-task case of the list-scheduling argument.
