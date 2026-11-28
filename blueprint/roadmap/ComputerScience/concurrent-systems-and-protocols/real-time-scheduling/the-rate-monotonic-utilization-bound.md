# The rate-monotonic utilization bound

In the Liu–Layland periodic task model with $m \ge 1$ periodic tasks (over intervals in which no non-periodic routine runs), every task set with processor utilization $U = \sum_i C_i/T_i \le m(2^{1/m} - 1)$ is schedulable by the rate-monotonic priority assignment whatever the phases of the tasks, and this threshold is the largest with this property: for every $\varepsilon > 0$ there is a set of $m$ tasks with utilization below $m(2^{1/m} - 1) + \varepsilon$ that the rate-monotonic assignment does not schedule for some choice of the phases. The threshold decreases to $\ln 2$ as $m \to \infty$. Task sets above the threshold can still be schedulable whatever the phases; for example, harmonic periods allow utilization $1$.

## Depends on

- [The Liu–Layland periodic task model](the-liu-layland-periodic-task-model.md)
- [Preemptive priority-driven schedules](periodic-task-model/produce-schedule.md)
- [Fixed-priority rules](periodic-task-model/is-fixed-priority.md)

## Proof depends on

- [Optimality of rate-monotonic priorities](optimality-of-rate-monotonic-priorities.md)

## Sources

- C. L. Liu and J. W. Layland, "Scheduling algorithms for multiprogramming in a hard-real-time environment", *Journal of the ACM* 20(1):46–61, 1973, Section 5, Theorems 3–5 and the definition of full utilization, and Section 6 (harmonic periods)
