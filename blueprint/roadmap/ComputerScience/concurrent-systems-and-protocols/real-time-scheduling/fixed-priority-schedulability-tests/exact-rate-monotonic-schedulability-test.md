# Exact rate-monotonic schedulability test

Let $\tau_1, \dots, \tau_n$ be tasks of the [Liu–Layland periodic task model](../the-liu-layland-periodic-task-model.md) with run-times $C_j$ and periods $T_j$, indexed so that $T_1 \le T_2 \le \dots \le T_n$ and scheduled by the rate-monotonic algorithm with $\tau_1$ of highest priority (ties between equal periods broken by index). For $1 \le i \le n$ let $R_i = \{(k, l) : 1 \le k \le i,\ l = 1, \dots, \lfloor T_i/T_k \rfloor\}$ be the scheduling points of $\tau_i$. All tasks meet all their deadlines for all task phasings if and only if for every $i$

$$
\min_{(k,l) \in R_i} \ \sum_{j=1}^{i} \frac{C_j}{l T_k} \left\lceil \frac{l T_k}{T_j} \right\rceil \le 1 .
$$

The sum is the processor demand of jobs of $\tau_1, \dots, \tau_i$ released in the half-open window $[0, lT_k)$ after a critical instant, divided by the window length. A release at $lT_k$ does not count towards this demand. The test checks whether the demand is met at some scheduling point no later than the deadline $T_i$.

## Depends on

- [The Liu–Layland periodic task model](../the-liu-layland-periodic-task-model.md)
- [Preemptive priority-driven schedules](../produce-schedule.md)
- [Fixed-priority rules](../is-fixed-priority.md)

## Proof depends on

- [The critical instant theorem](../the-critical-instant-theorem.md)

## Sources

- L. Sha, R. Rajkumar and J. P. Lehoczky, "Priority inheritance protocols: an approach to real-time synchronization", *IEEE Transactions on Computers* 39(9):1175–1185, 1990, Section V, Theorem 15, stated there as the exact characterization proved by Lehoczky, Sha and Ding (1989).
