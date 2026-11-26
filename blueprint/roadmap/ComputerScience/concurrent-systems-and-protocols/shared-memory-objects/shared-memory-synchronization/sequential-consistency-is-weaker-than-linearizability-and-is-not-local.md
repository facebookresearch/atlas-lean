# Sequential consistency is weaker than linearizability and is not local

Every linearizable history is sequentially consistent. There is a well-formed single-register history that is sequentially consistent but not linearizable, and there is a two-register history whose restriction to each register is sequentially consistent while the whole history is not; hence, unlike linearizability, sequential consistency is not a local property.

## Proof sketch

A read returning an old value after a write completed in real time can be explained by reordering processes but not by real time. For non-locality, two processes each write one register and then read the other's initial value; each register's history is consistent separately but no single interleaving explains both reads.

## Depends on

- [Sequential consistency of concurrent histories](sequential-consistency-of-concurrent-histories.md)
- [Linearizability](../linearizability.md)

## Proof depends on

- [Locality of linearizability](../locality-of-linearizability.md)

## Sources

- Maurice P. Herlihy and Jeannette M. Wing, "Linearizability: A Correctness Condition for Concurrent Objects", ACM Transactions on Programming Languages and Systems, 1990.
