# Observed-remove sets and the impossibility of untagged convergent sets

In the observed-remove set CRDT, each add creates a unique tag and a remove deletes only the tags it has observed; concurrent add and remove operations commute, an element is present iff some add of it is not causally followed by a remove observing its tag (add wins over concurrent remove), and all replicas that have delivered the same operations converge. By contrast, no state-based replicated set whose state is just a finite set of elements, merged by any function, can satisfy the sequential specification of insert and remove: the states $\{a\}$ and $\emptyset$ must merge to $\{a\}$ when the empty replica never saw $a$, and to $\emptyset$ when it received the insert of $a$ and then erased $a$, so no function of the two states alone is correct.

## Proof sketch

Tags make removes refer to specific adds, so the effect of concurrent operations is independent of delivery order. Without tags, let replica $A$ insert $a$ while replica $B$ either does nothing or receives $A$'s state and then erases $a$; in both runs the states to merge are $\{a\}$ and $\emptyset$, but the specification requires $\{a\}$ in the first and $\emptyset$ in the second.

## Depends on

- [Counter and set CRDTs](../counter-and-set-crdts.md)
- [Convergence of operation-based CRDTs](../convergence-of-operation-based-crdts.md)
- [Convergence of state-based CRDTs](../convergence-of-state-based-crdts.md)

## Sources

- Marc Shapiro, Nuno Preguiça, Carlos Baquero and Marek Zawirski, "Conflict-free Replicated Data Types", Stabilization, Safety, and Security of Distributed Systems (SSS 2011), 2011.
- Marc Shapiro, Nuno Preguiça, Carlos Baquero and Marek Zawirski, "A comprehensive study of Convergent and Commutative Replicated Data Types", INRIA, 2011.
