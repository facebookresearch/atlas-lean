# Tightness of the hyperbolic bound

For every list of rational utilizations $U_1, \dots, U_n$ with $0 < U_i \le 1$ and $\prod_{i=1}^{n} (U_i + 1) > 2$ there is a set of tasks $\tau_1, \dots, \tau_n$ of the [Liu–Layland periodic task model](../the-liu-layland-periodic-task-model.md) with $C_i/T_i = U_i$ that is not schedulable by the rate-monotonic algorithm. So [the hyperbolic bound](the-hyperbolic-bound-for-rate-monotonic-scheduling.md) is the best possible schedulability test that uses only the individual utilizations. The task set is built by choosing $T_1$ so that the following run-times and periods are natural numbers, which is possible as the $U_i$ are rational, and setting $C_i = U_i T_i$ and $T_{i+1} = T_i + C_i$ for $i < n$. The source allows every real $0 \le U_i \le 1$, with real run-times and periods; in this model run-times and periods are natural numbers, with $C_i \ge 1$, so the utilizations are rational and positive.

## Depends on

- [The Liu–Layland periodic task model](../the-liu-layland-periodic-task-model.md)
- [Preemptive priority-driven schedules](../produce-schedule.md)
- [Fixed-priority rules](../is-fixed-priority.md)
- [The hyperbolic bound for rate-monotonic scheduling](the-hyperbolic-bound-for-rate-monotonic-scheduling.md)

## Sources

- E. Bini, G. C. Buttazzo and G. M. Buttazzo, "Rate monotonic analysis: the hyperbolic bound", *IEEE Transactions on Computers* 52(7):933–942, 2003, Section 2, Theorem 2 and its proof (equations (9)).
