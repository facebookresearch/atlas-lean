# The basic priority inheritance protocol

In the model of [jobs sharing binary semaphores](jobs-sharing-binary-semaphores.md), the *basic priority inheritance protocol* is the following set of rules.

1. The job $J$ with the highest priority among the jobs ready to run is assigned the processor. Before $J$ enters a critical section it must obtain the lock on the semaphore $S$ guarding it. If $S$ is already locked, $J$ is blocked by the job holding the lock and the lock is denied; otherwise $J$ obtains the lock and enters the critical section. When $J$ exits the critical section, $S$ is unlocked and the highest-priority job blocked on $S$, if any, is awakened.
2. A job uses its assigned priority, unless it is in a critical section and blocks higher-priority jobs. If $J$ blocks higher-priority jobs it *inherits* the highest priority of the jobs it blocks; when $J$ exits a critical section it resumes the priority it had when it entered that critical section.
3. Priority inheritance is transitive: if $J_3$ blocks $J_2$ and $J_2$ blocks $J_1$, then $J_3$ inherits the priority of $J_1$ via $J_2$. The operations of priority inheritance and of the resumption of a previous priority are indivisible.
4. A job $J$ can preempt another job $J_L$ if $J$ is not blocked and its priority is higher than the priority, inherited or assigned, at which $J_L$ is executing.

Under this protocol a high-priority job can be blocked by a lower-priority one through *direct blocking*, when it tries to lock a locked semaphore, or through *push-through blocking*, when a medium-priority job is kept from running by a low-priority job that inherited a higher priority.

## Depends on

- [Jobs sharing binary semaphores](jobs-sharing-binary-semaphores.md)

## Sources

- L. Sha, R. Rajkumar and J. P. Lehoczky, "Priority inheritance protocols: an approach to real-time synchronization", *IEEE Transactions on Computers* 39(9):1175–1185, 1990, Section III.A (the definition of the basic protocol, rules 1–4 and the two kinds of blocking).
