# Mutual exclusion for n processes needs n registers

Every protocol that solves [the mutual exclusion problem](the-mutual-exclusion-problem.md), with mutual exclusion and deadlock freedom, for $n \ge 2$ processes in [the asynchronous shared-memory model](../shared-memory-objects/the-asynchronous-shared-memory-model.md) whose base objects are read/write registers uses at least $n$ registers. The proof is a covering argument.

## Depends on

- [The mutual exclusion problem](the-mutual-exclusion-problem.md)
- [The asynchronous shared-memory model](../shared-memory-objects/the-asynchronous-shared-memory-model.md)

## Sources

- H. Attiya and F. Ellen, *Impossibility Results for Distributed Computing*, Morgan & Claypool, 2014, Chapter 6 ("Covering arguments"), <https://www.cs.toronto.edu/~faith/chapter6.pdf>, Section 6.1: Lemma 6.1, Lemma 6.2 and Theorem 6.3, which credits J. E. Burns and N. A. Lynch, "Bounds on shared memory for mutual exclusion", *Information and Computation* 107:171–184, 1993.
- J. Aspnes, *Notes on Theory of Distributed Systems*, arXiv:2001.04235, <https://arxiv.org/abs/2001.04235>, Section 18.7 ("Space complexity"), Lemma 18.7.1.
