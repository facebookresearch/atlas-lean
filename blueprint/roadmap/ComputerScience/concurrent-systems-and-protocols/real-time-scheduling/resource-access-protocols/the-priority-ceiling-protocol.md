# The priority ceiling protocol

In the model of [jobs sharing binary semaphores](jobs-sharing-binary-semaphores.md), the *priority ceiling* of a semaphore is the priority of the highest-priority job that may lock it. The *priority ceiling protocol* is the following set of rules.

1. The job $J$ with the highest priority among the jobs ready to run is assigned the processor. Let $S^*$ be the semaphore with the highest priority ceiling among all semaphores currently locked by jobs other than $J$. Before $J$ enters a critical section it must obtain the lock on the semaphore $S$ guarding it. $J$ is blocked, and the lock on $S$ denied, if the priority of $J$ is not higher than the priority ceiling of $S^*$; $J$ is then said to be blocked on $S^*$, by the job holding the lock on $S^*$. Otherwise $J$ obtains the lock on $S$ and enters the critical section. When $J$ exits its critical section, the semaphore is unlocked and the highest-priority job, if any, blocked by $J$ is awakened.
2. A job uses its assigned priority, unless it is in a critical section and blocks higher-priority jobs. If $J$ blocks higher-priority jobs, $J$ inherits the highest priority of the jobs blocked by $J$; when $J$ exits a critical section, it resumes the priority it had at the point of entry into that critical section. Priority inheritance is transitive, and the operations of priority inheritance and of the resumption of a previous priority are indivisible.
3. A job $J$ that does not attempt to enter a critical section can preempt another job $J_L$ if its priority is higher than the priority, inherited or assigned, at which $J_L$ is executing.

Besides direct and push-through blocking, the protocol introduces *ceiling blocking*: a job may be denied a free semaphore because of a locked one with a high ceiling.

## Depends on

- [Jobs sharing binary semaphores](jobs-sharing-binary-semaphores.md)

## Sources

- L. Sha, R. Rajkumar and J. P. Lehoczky, "Priority inheritance protocols: an approach to real-time synchronization", *IEEE Transactions on Computers* 39(9):1175–1185, 1990, Section IV.A (the priority ceiling of a semaphore) and Section IV.B (the definition of the protocol, rules 1–3, and ceiling blocking).
