# Valency arguments for consensus

Consider a consensus protocol for $n \ge 2$ processes in the asynchronous shared-memory model, in which each process is deterministic, every base object has a deterministic sequential specification, and every process starts with an input value. The protocol is required to be *consistent* (distinct processes never decide distinct values), *wait-free* (each process decides after a finite number of its own steps) and *valid* (the common decision value is the input of some process). Fix such a protocol with inputs in $\{0, 1\}$ and consider configurations reachable from its initial configurations.

A configuration is *bivalent* if it can be extended by executions of the protocol to decide $0$ and also to decide $1$, and *univalent* otherwise; a univalent configuration is *$x$-valent* when $x$ is the decision value of all its extensions. A *decision step* is a step that carries the protocol from a bivalent to a univalent configuration, and a configuration is *critical* if it is bivalent and the next step of every process from it is a decision step.

## Depends on

- [The asynchronous shared-memory model](the-asynchronous-shared-memory-model.md)
- [Progress conditions for concurrent implementations](progress-conditions-for-concurrent.md)

## Sources

- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13(1):124–149, 1991, Section 2 (consensus protocols) and Section 3.1 (bivalent, univalent and x-valent states, decision steps)
