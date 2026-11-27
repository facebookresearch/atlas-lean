# The priority ceiling protocol prevents deadlock

Under [the priority ceiling protocol](the-priority-ceiling-protocol.md), in the model of [jobs sharing binary semaphores](jobs-sharing-binary-semaphores.md) (properly nested critical sections, no job locking a semaphore it already holds, no self-suspension), no deadlock can occur, whatever the order in which the jobs lock their semaphores. The protocol also prevents transitive blocking: no job is blocked by a job that is itself blocked by another job. The proof first shows that a job that preempts the critical section of another job and enters its own critical section cannot be blocked by it, so that the preempted job cannot inherit a priority at least as high as the preempting job's until the latter completes; a cycle of waiting jobs would then have length two, which contradicts this.

## Depends on

- [The priority ceiling protocol](the-priority-ceiling-protocol.md)

## Sources

- L. Sha, R. Rajkumar and J. P. Lehoczky, "Priority inheritance protocols: an approach to real-time synchronization", *IEEE Transactions on Computers* 39(9):1175–1185, 1990, Section IV.C, Lemmas 7–9 and Theorem 10, with the remark that follows it.
