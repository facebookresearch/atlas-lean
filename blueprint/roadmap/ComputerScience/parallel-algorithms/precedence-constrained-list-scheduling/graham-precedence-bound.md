# Graham's bound for list scheduling with precedence constraints

Every greedy schedule of a job system with precedence constraints on $m$ machines has makespan $C$ satisfying

$$
m \cdot C \le \sum_j p_j + (m - 1) \cdot \mathrm{span},
$$

hence $C \le (2 - 1/m)\, C^*$ where $C^*$ is the optimal makespan; greedy schedules always exist.

## Proof sketch

Walk backwards from the job finishing last: at every slot either all machines are busy or some job of a chain ending at that job is running, which yields a chain covering all non-full slots. Both $\sum_j p_j / m$ and the span are lower bounds on $C^*$.

## Depends on

- [Greedy schedules with precedence constraints](greedy-precedence-schedules.md)
- [Approximation algorithms and approximation ratios](../../approximation-algorithms/approximation-algorithms-and-approximation-ratios.md)

## Proof depends on

- [Graham's bound for list scheduling](../../approximation-algorithms/list-scheduling-on-identical-machines/list-schedule-approx.md)
- [Brent's theorem with the work and span laws](../work-span-model-and-brent-s-theorem/brent.md)

## Sources

- R. L. Graham, "Bounds for Certain Multiprocessing Anomalies", Bell System Technical Journal 45(9), 1966.
- R. L. Graham, "Bounds on Multiprocessing Timing Anomalies", SIAM Journal on Applied Mathematics 17(2), 1969.
