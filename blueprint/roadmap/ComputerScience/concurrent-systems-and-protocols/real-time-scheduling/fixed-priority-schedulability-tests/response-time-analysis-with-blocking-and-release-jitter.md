# Response-time analysis with blocking and release jitter

Consider [sporadic tasks](constrained-deadline-sporadic-tasks.md) $\tau_i = (C_i, T_i, D_i)$ with $D_i \le T_i$ scheduled by preemptive fixed priorities on one processor, where each job of $\tau_i$ is released at most $J_i$ after its arrival and is blocked by lower-priority jobs for at most $B_i$ in total (as under the [priority ceiling protocol](../resource-access-protocols/the-priority-ceiling-protocol.md), where $B_i$ is the longest critical section of a lower-priority task on a semaphore with ceiling at least the priority of $\tau_i$). Let $r_i$ be the least solution of

$$
r_i = C_i + B_i + \sum_{j \in hp(i)} \left\lceil \frac{r_i + J_j}{T_j} \right\rceil C_j ,
$$

if one exists; the iteration from $r_i^0 = 0$ reaches it, and may be stopped once an iterate exceeds $D_i - J_i$, since then no solution satisfies the test. If a solution exists and $J_i + r_i \le D_i$, then every job of $\tau_i$ completes within $J_i + r_i$ of its arrival, that is, within $r_i$ of its release.

## Depends on

- [Constrained-deadline sporadic tasks](constrained-deadline-sporadic-tasks.md)

## Proof depends on

- [Releases of a sporadic task in a window](releases-of-a-sporadic-task-in-a-window.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- the critical instant with release jitter: the worst case for $\tau_i$ arises when each higher-priority task has a job released at the end of its jitter window together with $\tau_i$ and the following jobs released without jitter (the source argues it on an example, Figure 4);
- that blocking under the priority ceiling protocol occurs at most once and adds at most $B_i$ to the busy period.

## Sources

- N. Audsley, A. Burns, M. Richardson, K. Tindell and A. J. Wellings, "Applying new scheduling theory to static priority pre-emptive scheduling", *Software Engineering Journal* 8(5):284–292, 1993; author version <https://www.math.unipd.it/~tullio/RTS/2009/ABRTW-1993.pdf>, Section 3, equations (1)–(3) (blocking term and the iteration), and Section 4, equations (5)–(6) (release jitter).
