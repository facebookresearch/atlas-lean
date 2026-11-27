# The mutual exclusion problem

In [the asynchronous shared-memory model](../shared-memory-objects/the-asynchronous-shared-memory-model.md), the states of each process are partitioned into four regions: *remainder*, *trying*, *critical* and *exit*. From the remainder region a process moves only into the trying or critical region, and from the trying region it stays in the trying region until it enters the critical region; from the critical region it moves only into the exit or remainder region, and from the exit region it stays there until it reaches the remainder region. A mutual exclusion protocol consists of the steps processes take in their trying and exit regions. It satisfies

- *mutual exclusion* if no reachable configuration has two processes in their critical regions;
- *deadlock freedom* and *starvation freedom* in the sense of the [progress conditions](../shared-memory-objects/progress-conditions-for-concurrent.md) for mutual exclusion, which are required only over fair executions without crashes in which every process that enters its critical region eventually leaves it.

It *solves the mutual exclusion problem* if it satisfies mutual exclusion and deadlock freedom.

## Depends on

- [The asynchronous shared-memory model](../shared-memory-objects/the-asynchronous-shared-memory-model.md)
- [Progress conditions for concurrent implementations](../shared-memory-objects/progress-conditions-for-concurrent.md)

## Sources

- J. E. Burns, M. J. Fischer, P. Jackson, N. A. Lynch and G. L. Peterson, "Data requirements for implementation of N-process mutual exclusion using a single shared variable", *Journal of the ACM* 29(1):183–205, 1982, <https://groups.csail.mit.edu/tds/papers/Lynch/jacm82.pdf>, Section 2.1 (processes whose states are partitioned into remainder, trying, critical and exit regions, with conditions (a)–(d) on their transitions, and admissible schedules, in which no process halts outside its remainder region) and Section 2.2 (C1, mutual exclusion; C2, deadlock freedom; C3, lockout freedom).
- J. Aspnes, *Notes on Theory of Distributed Systems*, arXiv:2001.04235, <https://arxiv.org/abs/2001.04235>, Chapter 18 ("Mutual exclusion"), Sections 18.1 ("The problem") and 18.2 ("Goals").
