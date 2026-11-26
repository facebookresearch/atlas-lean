# Observed-remove sets and the impossibility of untagged convergent sets

In the observed-remove set CRDT, each add creates a unique tag and a remove deletes only the tags it has observed; concurrent add and remove operations commute, an element is present iff some add of it is not causally followed by a remove observing its tag (add wins over concurrent remove), and all replicas that have delivered the same operations converge. By contrast, no state-based replicated set whose state is just a finite set of elements, merged by any function, can satisfy the sequential specification of insert and remove: insert-then-erase and erase-then-insert must give different results, which no commutative merge of untagged states can distinguish.

## Proof sketch

Tags make removes refer to specific adds, so the effect of concurrent operations is independent of delivery order. Without tags, the merge of a replica that inserted and erased with one that did nothing equals the merge for the reverse order, contradicting the specification.

## Depends on

- [Counter and set CRDTs](../replication-and-consistency/counter-and-set-crdts.md)
- [Convergence of operation-based CRDTs](../replication-and-consistency/convergence-of-operation-based-crdts.md)
- [Convergence of state-based CRDTs](../replication-and-consistency/convergence-of-state-based-crdts.md)

## Sources

- Marc Shapiro, Nuno Preguiça, Carlos Baquero and Marek Zawirski, "Conflict-free Replicated Data Types", Stabilization, Safety, and Security of Distributed Systems (SSS 2011), 2011.
- Marc Shapiro, Nuno Preguiça, Carlos Baquero and Marek Zawirski, "A comprehensive study of Convergent and Commutative Replicated Data Types", INRIA, 2011.
