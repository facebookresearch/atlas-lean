# The greedy scheduling bound

Let $G$ be a computation DAG with $n$ tasks and span $D$, and
let $S$ be a greedy schedule of $G$ on $p$ processors taking $T$ steps. Then
$pT \le n + (p - 1)D$.

Each complete step runs $p$ tasks, and each of the at most $D$ incomplete steps runs at least one.

## Sources

- the unit-task case of Graham's list-scheduling argument, Graham, *Bounds for certain multiprocessing anomalies*, Bell System Tech. J. 45, 1966.
