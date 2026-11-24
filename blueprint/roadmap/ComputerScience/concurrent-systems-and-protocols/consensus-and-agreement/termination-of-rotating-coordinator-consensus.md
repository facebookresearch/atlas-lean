# Termination of rotating-coordinator consensus with an eventually strong detector

In Chandra and Toueg's rotating-coordinator consensus algorithm for $n$ asynchronous processes with reliable channels and fewer than $n/2$ crashes, if the failure detector belongs to the class $\Diamond\mathcal{S}$ (strong completeness and eventual weak accuracy), every correct process eventually decides.

## Depends on

- [Weak and strong fairness](../distributed-execution-models/weak-and-strong-fairness.md)

## Proof depends on

- [Safety of rotating-coordinator consensus](safety-of-rotating-coordinator-consensus.md)

## Sources

- T. D. Chandra and S. Toueg, "Unreliable failure detectors for reliable distributed systems", *Journal of the ACM* 43(2):225–267, 1996
- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, 2020, <https://arxiv.org/abs/2001.04235>
