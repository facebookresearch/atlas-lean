# Rate-monotonic utilization test under the priority ceiling protocol

Let $\tau_1, \dots, \tau_n$ be periodic tasks, indexed by nondecreasing period and given rate-monotonic priorities, whose jobs share binary semaphores under [the priority ceiling protocol](the-priority-ceiling-protocol.md). Each job of $\tau_i$ has a deterministic execution time $C_i$ for its critical and noncritical sections, does not synchronize with external events, and executes to completion when it is the only job in the system; $T_i$ is the period of $\tau_i$, and $B_i$ is the worst-case blocking time of a job of $\tau_i$, the duration of the longest element of $\beta^*_i$ ($B_n = 0$). If

$$
\frac{C_1}{T_1} + \frac{C_2}{T_2} + \dots + \frac{C_i}{T_i} + \frac{B_i}{T_i} \le i\left(2^{1/i} - 1\right) \qquad \text{for every } 1 \le i \le n,
$$

then every job of every task meets its deadline, the next request of its task. A simpler sufficient condition is $\sum_{i=1}^{n} C_i/T_i + \max(B_1/T_1, \dots, B_{n-1}/T_{n-1}) \le n(2^{1/n} - 1)$.

**Proof.** Fix $i$. The condition is the [rate-monotonic utilization bound](../the-rate-monotonic-utilization-bound.md) for the tasks $\tau_1, \dots, \tau_i$ with $C_i$ replaced by $C_i + B_i$, so without blocking a job of $\tau_i$ would meet its deadline even if it executed for $C_i + B_i$; since it executes for $C_i$ and is [blocked for at most $B_i$](the-priority-ceiling-protocol-blocks-a-job-at-most-once.md), it meets its deadline.

## Depends on

- [The Liu–Layland periodic task model](../the-liu-layland-periodic-task-model.md)
- [The priority ceiling protocol](the-priority-ceiling-protocol.md)

## Proof depends on

- [The rate-monotonic utilization bound](../the-rate-monotonic-utilization-bound.md)
- [The priority ceiling protocol blocks a job at most once](the-priority-ceiling-protocol-blocks-a-job-at-most-once.md)

## Sources

- L. Sha, R. Rajkumar and J. P. Lehoczky, "Priority inheritance protocols: an approach to real-time synchronization", *IEEE Transactions on Computers* 39(9):1175–1185, 1990, Section V: the scheduling model, Theorem 14 (the Liu–Layland bound), Theorem 16 with its proof, and Corollary 17.
