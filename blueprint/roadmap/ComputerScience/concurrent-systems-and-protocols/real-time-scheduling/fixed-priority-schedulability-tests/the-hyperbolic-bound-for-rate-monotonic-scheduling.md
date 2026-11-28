# The hyperbolic bound for rate-monotonic scheduling

Let $\tau_1, \dots, \tau_n$ be tasks of the [Liu–Layland periodic task model](../the-liu-layland-periodic-task-model.md) with utilizations $U_i = C_i/T_i$. If

$$
\prod_{i=1}^{n} (U_i + 1) \le 2,
$$

then the task set is schedulable by the rate-monotonic algorithm whatever the phases: for every choice of the phases, no request ever overflows.

The test needs only the utilizations, as the [rate-monotonic utilization bound](../the-rate-monotonic-utilization-bound.md) $\sum_i U_i \le n(2^{1/n} - 1)$ does, and accepts every task set that bound accepts: by the inequality of arithmetic and geometric means, $\prod_i (U_i + 1) \le (1 + \frac{1}{n}\sum_i U_i)^n \le 2$ whenever $\sum_i U_i \le n(2^{1/n} - 1)$.

## Depends on

- [The Liu–Layland periodic task model](../the-liu-layland-periodic-task-model.md)
- [Preemptive priority-driven schedules](../periodic-task-model/produce-schedule.md)
- [Fixed-priority rules](../periodic-task-model/is-fixed-priority.md)

## Proof depends on

- [The critical instant theorem](../the-critical-instant-theorem.md): the proof reduces to the worst-case configuration in which all tasks are requested together and $T_1 < T_i < 2T_1$ for $i \ge 2$.

## Sources

- E. Bini, G. C. Buttazzo and G. M. Buttazzo, "Rate monotonic analysis: the hyperbolic bound", *IEEE Transactions on Computers* 52(7):933–942, 2003, Section 2, Theorem 1 and its proof.
