# The mutual exclusion problem

In [the asynchronous shared-memory model](../shared-memory-objects/the-asynchronous-shared-memory-model.md), each process cycles through four states: *remainder*, *trying*, *critical* and *exiting*. A mutual exclusion protocol decides when a process moves on from the trying and exiting states; a process moves from the remainder state to the trying state, and from the critical state to the exiting state, on its own. The protocol solves the *mutual exclusion problem* if it guarantees:

- *mutual exclusion*: at most one process is in the critical state at any time;
- *deadlock freedom*: if some process is in the trying state, then eventually some process enters the critical state, and similarly some process in the exiting state eventually reaches the remainder state, provided that processes leave the critical state on their own.

The protocol is *starvation-free* if, in addition, every process in the trying or exiting state eventually leaves that state.

## Depends on

- [The asynchronous shared-memory model](../shared-memory-objects/the-asynchronous-shared-memory-model.md)

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, arXiv:2001.04235, <https://arxiv.org/abs/2001.04235>, Chapter 18 ("Mutual exclusion"), Sections 18.1 ("The problem") and 18.2 ("Goals").
