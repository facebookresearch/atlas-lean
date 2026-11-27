# Mutual exclusion yields linearizable objects

Let an object be given by a sequential implementation in which an operation reads the whole state $q$ of the object from a register $r$, writes $f(q)$ back and returns $q$. If each operation runs this code inside the critical section of a protocol that guarantees mutual exclusion (see [The mutual exclusion problem](the-mutual-exclusion-problem.md)), every history of the resulting concurrent implementation is [linearizable](../shared-memory-objects/linearizability.md): ordering the operations by the times they enter the critical section gives a linearization.

## Depends on

- [The mutual exclusion problem](the-mutual-exclusion-problem.md)
- [Linearizability](../shared-memory-objects/linearizability.md)

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, arXiv:2001.04235v6 (18 May 2026), <https://arxiv.org/abs/2001.04235v6>, Section 18.4 ("Mutual exclusion and linearizability"), Algorithm 18.4 and the argument after it, pp. 155–156.
