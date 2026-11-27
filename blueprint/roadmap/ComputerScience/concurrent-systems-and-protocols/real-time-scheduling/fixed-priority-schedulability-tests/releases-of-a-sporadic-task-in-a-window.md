# Releases of a sporadic task in a window

Let a [sporadic task](constrained-deadline-sporadic-tasks.md) $\tau_j$ have minimum inter-arrival time $T_j > 0$ and release jitter at most $J_j \ge 0$: each job is released within $J_j$ of its arrival. Then any time window $[t, t + r)$ of length $r > 0$ contains at most $\lceil r/T_j \rceil$ arrivals of $\tau_j$, and at most $\lceil (r + J_j)/T_j \rceil$ releases. Hence the jobs of $\tau_j$ released in the window, each with execution time at most $C_j$, need at most $\lceil (r + J_j)/T_j \rceil C_j$ units of execution in total, or $\lceil r/T_j \rceil C_j$ without jitter, whether $\tau_j$ is periodic or sporadic. This bounds the interference of a higher-priority task $\tau_j$ on a lower-priority job during the window only when no job of $\tau_j$ released before the window still has work left at its start, as at a critical instant: otherwise carry-in adds to it. For example, with $T_j = 10$ and $C_j = 5$, jobs released at $0$ and $10$ and a still higher-priority task busy on $[0, 5)$, $\tau_j$ executes for $10$ units in the window $[5, 15)$ of length $10$.

**Proof.** Arrivals in $[t, t + r)$ are at least $T_j$ apart, so if there are $n$ of them then $(n - 1)T_j < r$. Releases in the window come from arrivals in $[t - J_j, t + r)$, a window of length $r + J_j$.

## Depends on

- [Constrained-deadline sporadic tasks](constrained-deadline-sporadic-tasks.md)

## Sources

- N. Audsley, A. Burns, M. Richardson, K. Tindell and A. J. Wellings, "Applying new scheduling theory to static priority pre-emptive scheduling", *Software Engineering Journal* 8(5):284–292, 1993; author version <https://www.math.unipd.it/~tullio/RTS/2009/ABRTW-1993.pdf>, Section 3 (the interference $\lceil r_i/T_j\rceil C_j$ and the remark that it holds for sporadic tasks) and Section 4 (equation (5) and the extra hit caused by release jitter).
