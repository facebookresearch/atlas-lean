# Lamport's bakery over safe registers: first-come-first-served and starvation freedom

Lamport's bakery algorithm remains correct when the single-writer registers $\mathit{choosing}[i]$ and $\mathit{number}[i]$ are merely safe (reads overlapping a write may return any value) and processes may fail and recover: it guarantees mutual exclusion, and it is first-come-first-served, in that a process that completes its doorway before another starts its doorway enters the critical section first. Under weak per-process fairness and a finite bound on the number of failures, every trying process that does not fail eventually enters the critical section.

## Proof sketch

A process finishing its doorway before another starts makes the latter read a larger ticket, giving first-come-first-served. Once failures stop, tickets of processes behind a waiting process increase, so the waiting process eventually holds the minimum (ticket, identifier) pair among those trying.

## Depends on

- [Mutual exclusion for the bakery algorithm](../../bakery-algorithm/mutual-exclusion.md)
- [The bakery algorithm as a labelled transition system](../../bakery-algorithm/lts.md)
- [Weak and strong fairness](../../distributed-execution-models/weak-and-strong-fairness.md)

## Sources

- Leslie Lamport, "A New Solution of Dijkstra's Concurrent Programming Problem", Communications of the ACM, 1974.
