# Cardinality conditions for threshold Byzantine quorum systems and masking-register safety

For the family of all subsets of size $q$ of $n$ servers, the system is a dissemination quorum system against $b$ faults iff $2q - n \ge b + 1$ and $q \le n - b$ (feasible iff $n > 3b$), and a masking quorum system iff $2q - n \ge 2b + 1$ and $q \le n - b$ (feasible iff $n > 4b$). In a masking quorum system, a read that is not concurrent with any write, which queries a quorum and accepts the highest-timestamped value reported by at least $b + 1$ servers, returns the latest completed write.

## Proof sketch

Two $q$-subsets of an $n$-set intersect in at least $2q - n$ elements, with equality attainable; availability requires a quorum among the $n - b$ correct servers. In a masking system the latest write's quorum meets the read quorum in at least $2b + 1$ servers, of which at least $b + 1$ are correct and report it, while faulty servers alone cannot reach $b + 1$.

## Depends on

- [Dissemination, masking and opaque Byzantine quorum systems](dissemination-masking-and-opaque-byzantine-quorum-systems.md)

## Sources

- Dahlia Malkhi and Michael Reiter, "Byzantine Quorum Systems", Distributed Computing, 1998.
