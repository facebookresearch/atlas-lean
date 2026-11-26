# Blocking under priority inheritance by lower-priority jobs

Under [the basic priority inheritance protocol](the-basic-priority-inheritance-protocol.md), in a system in which deadlock is prevented by some external means (for example, all jobs lock semaphores in an order consistent with a fixed acyclic order), let $J_0$ be a job and $J_1, \dots, J_n$ the jobs of lower priority. Then $J_0$ can be blocked for at most the duration of one critical section in each of $\beta^*_{0,1}, \dots, \beta^*_{0,n}$. Each lower-priority job $J_i$ can block $J_0$ only while it executes a critical section of $\beta^*_{0,i}$ that it was already executing when $J_0$ was initiated, and once it exits that critical section $J_0$ preempts it for good.

## Depends on

- [The basic priority inheritance protocol](the-basic-priority-inheritance-protocol.md)

## Sources

- L. Sha, R. Rajkumar and J. P. Lehoczky, "Priority inheritance protocols: an approach to real-time synchronization", *IEEE Transactions on Computers* 39(9):1175–1185, 1990, Section III.B, Lemmas 1 and 2 and Theorem 3.
