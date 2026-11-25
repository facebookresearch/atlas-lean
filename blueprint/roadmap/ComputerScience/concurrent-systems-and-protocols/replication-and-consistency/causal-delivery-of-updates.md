# Causal delivery of updates

A replicated system provides *causal delivery* if every replica delivers an update $u_2$ only after it has delivered every update $u_1$ that happened before $u_2$ at the replica where $u_2$ originated, where happened-before is the transitive closure of the replica-local order and the order from delivering an update to issuing a later one.

## Depends on

- [Happened-before](../lamport-clocks/happens-before.md)

## Sources

- M. Shapiro, N. Preguiça, C. Baquero and M. Zawirski, "Conflict-free replicated data types", *SSS 2011*, LNCS 6976, Springer, 2011; INRIA research report RR-7687
- L. Lamport, "Time, clocks, and the ordering of events in a distributed system", *Communications of the ACM* 21(7):558–565, 1978
