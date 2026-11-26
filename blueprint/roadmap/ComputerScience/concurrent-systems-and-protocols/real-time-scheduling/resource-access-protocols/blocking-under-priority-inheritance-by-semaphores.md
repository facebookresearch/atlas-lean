# Blocking under priority inheritance by semaphores

Under [the basic priority inheritance protocol](the-basic-priority-inheritance-protocol.md), in a system in which deadlock is prevented by some external means, if there are $m$ semaphores which can block a job $J$, then $J$ can be blocked at most $m$ times: at most once through each semaphore, by at most one critical section guarded by it. Together with [blocking by lower-priority jobs](blocking-under-priority-inheritance-by-lower-priority-jobs.md), a job with $n$ lower-priority jobs and $m$ semaphores that can block it is blocked for at most the duration of $\min(n, m)$ critical sections.

## Depends on

- [The basic priority inheritance protocol](the-basic-priority-inheritance-protocol.md)

## Proof depends on

- [Blocking under priority inheritance by lower-priority jobs](blocking-under-priority-inheritance-by-lower-priority-jobs.md): the bound by $n$ in $\min(n, m)$.

## Sources

- L. Sha, R. Rajkumar and J. P. Lehoczky, "Priority inheritance protocols: an approach to real-time synchronization", *IEEE Transactions on Computers* 39(9):1175–1185, 1990, Section III.B, Lemmas 4 and 5 and Theorem 6, and the bound $\min(n, m)$ stated in Section IV.B.
