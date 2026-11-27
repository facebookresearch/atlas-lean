# Deterministic processes are the maximal processes under refinement

A member of the [failures-divergences model](the-failures-divergences-model.md) $\mathcal{N}$ is maximal with respect to failures-divergences refinement $\sqsubseteq_{FD}$ if and only if it is [deterministic](deterministic-processes.md). In particular $\mathcal{N}$ has no greatest element, and every process $P \in \mathcal{N}$ is refined by some deterministic process.

## Depends on

- [Deterministic processes in CSP](deterministic-processes.md)
- [The failures-divergences model of CSP](the-failures-divergences-model.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 9.1: Lemma 9.1.1 (every member of $\mathcal{D}$ is maximal), Lemma 9.1.2 (deterministic processes correspond to trace sets in which no trace that can terminate is extended by an event) and Lemma 9.1.3 (every maximal element of $\mathcal{N}$ is deterministic), with the construction of a deterministic refinement of an arbitrary process between Lemmas 9.1.2 and 9.1.3.
