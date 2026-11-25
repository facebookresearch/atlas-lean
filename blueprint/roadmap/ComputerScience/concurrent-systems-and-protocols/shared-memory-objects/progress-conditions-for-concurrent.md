# Progress conditions for concurrent implementations

Consider an implementation of a concurrent object from base objects in the asynchronous shared-memory model.

- It is *wait-free* if every process finishes each of its operations in a bounded number of its own steps, whatever the other processes do.
- It is *lock-free* if infinitely many operations finish in every infinite execution.
- It is *obstruction-free* if, from every reachable configuration, any process finishes its operation in a bounded number of steps when all other processes stop taking steps.

For a mutual exclusion protocol, each process cycles through *trying*, *critical*, *exiting* and *remainder* states, runs the protocol only in its trying and exiting states, and leaves its critical and remainder states on its own. Over fair executions without crashes, the protocol is *deadlock-free* if, whenever some process is trying (respectively exiting), some process eventually enters its critical (respectively remainder) state, and *starvation-free* if every process that is trying or exiting eventually leaves that state.

## Depends on

- [The asynchronous shared-memory model](the-asynchronous-shared-memory-model.md)

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, 2020, <https://arxiv.org/abs/2001.04235>, the chapters on mutual exclusion (the problem and its goals) and on obstruction-freedom (its introduction defining lock-freedom and obstruction-freedom)
- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13(1):124–149, 1991
