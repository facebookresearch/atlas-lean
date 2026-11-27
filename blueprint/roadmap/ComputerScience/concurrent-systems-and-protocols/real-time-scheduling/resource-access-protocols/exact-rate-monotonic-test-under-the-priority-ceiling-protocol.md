# Exact rate-monotonic test under the priority ceiling protocol

In the setting of the [rate-monotonic utilization test under the priority ceiling protocol](rate-monotonic-utilization-test-under-the-priority-ceiling-protocol.md), with $U_j = C_j/T_j$ and the scheduling points $R_i = \{(k, l) : 1 \le k \le i,\ l = 1, \dots, \lfloor T_i/T_k \rfloor\}$, the periodic tasks can be scheduled by the rate-monotonic algorithm for all task phasings if for every $1 \le i \le n$

$$
\min_{(k,l) \in R_i} \left[ \sum_{j=1}^{i-1} U_j \frac{T_j}{l T_k} \left\lceil \frac{l T_k}{T_j} \right\rceil + \frac{C_i}{l T_k} + \frac{B_i}{l T_k} \right] \le 1 .
$$

Because $B_i$ is a worst-case bound, this condition is sufficient but not necessary; with $B_i = 0$ for all $i$ it is the [exact rate-monotonic schedulability test](../fixed-priority-schedulability-tests/exact-rate-monotonic-schedulability-test.md).

## Depends on

- [Rate-monotonic utilization test under the priority ceiling protocol](rate-monotonic-utilization-test-under-the-priority-ceiling-protocol.md)

## Proof depends on

- [Exact rate-monotonic schedulability test](../fixed-priority-schedulability-tests/exact-rate-monotonic-schedulability-test.md): applied with $C_i$ replaced by $C_i + B_i$.
- [The priority ceiling protocol blocks a job at most once](the-priority-ceiling-protocol-blocks-a-job-at-most-once.md)

## Sources

- L. Sha, R. Rajkumar and J. P. Lehoczky, "Priority inheritance protocols: an approach to real-time synchronization", *IEEE Transactions on Computers* 39(9):1175–1185, 1990, Section V, Theorem 18 and the remark following it.
