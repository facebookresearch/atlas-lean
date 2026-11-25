# The asynchronous shared-memory model

In the asynchronous shared-memory model, $n$ processes communicate through shared base objects such as atomic registers or read-modify-write objects. Each process is a state machine whose transition function chooses its next operation on a base object and how its state is updated by the operation's return value. A *configuration* consists of the states of the processes and of the base objects, and an *execution* is a finite or infinite sequence $C_0, \pi_1, C_1, \pi_2, C_2, \dots$ of configurations and operations in which each $C_{i+1}$ results from applying $\pi_{i+1}$, an operation of one process on one base object, to $C_i$. The schedule of processes is chosen by an adversary. An infinite execution is *fair* if every process performs an operation infinitely often unless it crashes or halts, after which it performs no further operations.

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, 2020, <https://arxiv.org/abs/2001.04235>, the chapter "Model" of Part II (shared memory), sections on atomic registers and on fairness and crashes
- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13(1):124–149, 1991
