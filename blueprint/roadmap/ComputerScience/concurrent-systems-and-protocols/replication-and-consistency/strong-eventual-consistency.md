# Strong eventual consistency

A history of a replicated object records the local state of each replica at every snapshot, the updates it receives, and the methods it starts and completes. Every update occurrence has a unique identifier, even if two updates have identical arguments. A replica's delivered set at a snapshot contains all update identifiers it has received before that snapshot. Repeated delivery of an identifier does not change the set. A replica can count its own updates as deliveries. State equivalence is specified by the object, for example by equality of query answers, rather than by equality of the stored representations.

The history satisfies **eventual consistency** if all three conditions hold:

- **Eventual delivery.** An update delivered to a correct replica eventually reaches every correct replica.
- **Eventual convergence.** If two correct replicas have equal delivered sets at every snapshot from some point onward, their states are equivalent at every snapshot from some later point onward. The delivered sets may continue to grow together.
- **Termination.** Every started method has a recorded completion at or after its start.

The history satisfies **strong eventual consistency** if it has eventual delivery, termination, and **strong convergence**: whenever two observations at correct replicas have equal delivered update sets, their states are already equivalent at those observations. The observations may be at different snapshots, so the rule compares the local history of each replica without requiring simultaneous observation. It also applies at the same snapshot; taking this case at each snapshot along a tail of equal delivered sets gives eventual convergence. Thus strong eventual consistency is equivalently eventual consistency plus strong convergence. An object has the property if all of its admissible histories satisfy it. These predicates do not prescribe a communication protocol.

## Background

- [Infinite run](../../process-calculi/labelled-transition-systems/omega-run.md)

## Sources

- M. Shapiro, N. Preguiça, C. Baquero and M. Zawirski, "Conflict-free replicated data types", *SSS 2011*, LNCS 6976, Springer, 2011, Definitions 2–3; [INRIA research report RR-7687](https://www.lip6.fr/Marc.Shapiro/papers/RR-7687.pdf), Definitions 2.2–2.3. Eventual convergence above uses the explicit same-snapshot tail convention.
