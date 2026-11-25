# Counter and set CRDTs

The G-Counter, whose state at each replica is a vector of per-replica counts with merge the pointwise maximum, increment adding one to the local entry and value the sum of the entries; the PN-Counter, a pair of G-Counters for increments and decrements with value their difference; and the G-Set and 2P-Set, with merge by union (of added elements, and for the 2P-Set also of removed elements), all satisfy the monotonic semilattice property: their states form a join-semilattice under the merge, and every update is inflationary. Treating each update as a distinct event (two increments by the same replica are different events), each is a state-based CRDT; under eventual delivery, in which every state is eventually merged into every correct replica, it is strongly eventually consistent.

## Depends on

- [Monotonic semilattice objects](monotonic-semilattice-objects.md)
- [Strong eventual consistency](strong-eventual-consistency.md)

## Proof depends on

- [Convergence of state-based CRDTs](convergence-of-state-based-crdts.md)

## Sources

- M. Shapiro, N. Preguiça, C. Baquero and M. Zawirski, "Conflict-free replicated data types", *SSS 2011*, LNCS 6976, Springer, 2011; INRIA research report RR-7687
