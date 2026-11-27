# Greedy schedules with precedence constraints

Jobs $J$ with integer processing times $p_j \ge 1$ and an acyclic precedence relation $\prec$ are to be run non-preemptively on $m$ identical machines in discrete time ($P \mid \mathrm{prec} \mid C_{\max}$). A schedule assigns start times $s_j$ such that $s_j \ge s_i + p_i$ whenever $i \prec j$ and at most $m$ jobs run in each unit slot. It is **greedy** (a Graham list schedule) if no machine is ever idle while some job is available, i.e. all its predecessors have finished and it has not started. The **span** is the maximum total processing time of a $\prec$-chain.

## Depends on

- [Brent's theorem with the work and span laws](../work-span-model-and-brent-s-theorem/brent.md)
- [Graham's list scheduling](../../approximation-algorithms/list-scheduling-on-identical-machines/list-schedule.md)

## Sources

- R. L. Graham, "Bounds for Certain Multiprocessing Anomalies", Bell System Technical Journal 45(9), 1966.
- R. L. Graham, "Bounds on Multiprocessing Timing Anomalies", SIAM Journal on Applied Mathematics 17(2), 1969.
