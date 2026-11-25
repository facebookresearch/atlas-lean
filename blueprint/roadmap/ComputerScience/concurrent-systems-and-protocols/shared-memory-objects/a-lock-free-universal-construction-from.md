# A lock-free universal construction from consensus

For every deterministic sequential object type there is a lock-free linearizable implementation for $n$ processes from $n$-process consensus objects and atomic registers: processes agree, slot by slot, on a log of operations by one consensus object per slot, and every process computes its operation's response by replaying the agreed log. Adding a helping mechanism, in which processes propose pending operations of others, makes the construction wait-free.

## Depends on

- [Linearizability](linearizability.md)
- [Consensus number](consensus-number.md)
- [Progress conditions for concurrent implementations](progress-conditions-for-concurrent.md)

## Sources

- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13(1):124–149, 1991
- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, 2020, <https://arxiv.org/abs/2001.04235>
