# Convergence of state-based CRDTs

Consider a state-based replicated object satisfying the monotonic semilattice property (its states form a join-semilattice, merge is the join and every update is inflationary). If every update is eventually delivered to every replica, directly or through merges, and all methods terminate, then the object satisfies strong eventual consistency. The algebraic core: every update is a uniquely identified event that inflates the payload state, all replicas start from a common initial state, and the payload state of a replica is the join of the initial state with the states produced by the update events it has received, so replicas that have received the same set of update events have equal payload states.

## Depends on

- [Monotonic semilattice objects](monotonic-semilattice-objects.md)
- [Strong eventual consistency](strong-eventual-consistency.md)

## Sources

- M. Shapiro, N. Preguiça, C. Baquero and M. Zawirski, "Conflict-free replicated data types", *SSS 2011*, LNCS 6976, Springer, 2011; INRIA research report RR-7687, Theorem 2.1
