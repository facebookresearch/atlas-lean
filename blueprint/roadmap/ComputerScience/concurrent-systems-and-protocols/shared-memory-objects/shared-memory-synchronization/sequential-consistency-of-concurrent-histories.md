# Sequential consistency of concurrent histories

A well-formed concurrent history over shared objects with prefix-closed sequential specifications is *sequentially consistent* if it can be completed and reordered into a legal sequential history that preserves the order of operations of each process, but not necessarily the real-time order between operations of different processes.

## Depends on

- [Concurrent histories](../concurrent-histories.md)
- [Prefix-closed and total sequential specifications](../sequential-specifications-of-objects.md)
- [Linearizability](../linearizability.md)

## Sources

- Maurice P. Herlihy and Jeannette M. Wing, "Linearizability: A Correctness Condition for Concurrent Objects", ACM Transactions on Programming Languages and Systems, 1990.
