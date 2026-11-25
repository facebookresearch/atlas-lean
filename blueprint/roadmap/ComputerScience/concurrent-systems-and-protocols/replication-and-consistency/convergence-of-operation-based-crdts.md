# Convergence of operation-based CRDTs

Consider an operation-based replicated object whose replicas start in a common initial state, in which every update is delivered exactly once to every replica, in causal order, and every method terminates. If all pairs of concurrent update operations commute, and every update's delivery precondition is satisfied under causal delivery, then the object satisfies strong eventual consistency: any two replicas that have delivered the same set of updates are in equivalent states. Causal delivery alone does not suffice when an update may be delivered twice, unless its operation is idempotent.

## Depends on

- [Causal delivery of updates](causal-delivery-of-updates.md)
- [Strong eventual consistency](strong-eventual-consistency.md)

## Sources

- M. Shapiro, N. Preguiça, C. Baquero and M. Zawirski, "Conflict-free replicated data types", *SSS 2011*, LNCS 6976, Springer, 2011; INRIA research report RR-7687, Theorem 2.2
