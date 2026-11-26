# The priority ceiling protocol blocks a job at most once

Under [the priority ceiling protocol](the-priority-ceiling-protocol.md), in the model of [jobs sharing binary semaphores](jobs-sharing-binary-semaphores.md), a job $J_i$ can be blocked for at most the duration of at most one element of $\beta^*_i$, the set of the longest critical sections of lower-priority jobs that can block it. If jobs may instead suspend themselves, a job that suspends itself $n$ times during its execution can be blocked by at most $n + 1$ elements of $\beta^*_i$, not necessarily distinct.

## Depends on

- [The priority ceiling protocol](the-priority-ceiling-protocol.md)

## Proof depends on

- [The priority ceiling protocol prevents deadlock](the-priority-ceiling-protocol-prevents-deadlock.md): a lower-priority job blocking $J_i$ eventually exits its critical section.

## Sources

- L. Sha, R. Rajkumar and J. P. Lehoczky, "Priority inheritance protocols: an approach to real-time synchronization", *IEEE Transactions on Computers* 39(9):1175–1185, 1990, Section IV.C, Lemma 11, Theorem 12 and Corollary 13.
