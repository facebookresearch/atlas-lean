# Consensus number

The *consensus number* of an object type $X$ is the largest $n$ such that objects of type $X$ together with atomic read/write registers can implement wait-free consensus among $n$ processes, or $\infty$ if there is no largest such $n$.

## Depends on

- [Progress conditions for concurrent implementations](progress-conditions-for-concurrent.md)
- [FLP impossibility of asynchronous consensus with agreement, validity and termination](../flp-impossibility/flp-impossibility.md)

## Sources

- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13(1):124–149, 1991, Definition 1
