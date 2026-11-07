# The work-span bound for greedy schedules

Let $G$ be a computation DAG with $n$ tasks and
span $D$, and let $S$ be a greedy schedule of $G$ on $p$ processors taking $T$ steps. Then
$pT \le n + pD$, that is, $T \le n/p + D$ when $p \ge 1$.

This is a weakening of the greedy scheduling bound $pT \le n + (p - 1)D$.

## Sources

- CLRS, third edition, Theorem 27.1.
