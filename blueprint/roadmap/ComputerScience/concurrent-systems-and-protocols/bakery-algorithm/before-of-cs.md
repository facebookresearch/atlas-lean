# Assertion 2 of the bakery proof

In every state reachable from the [initial state](init.md) of the [bakery algorithm](lts.md): if process $i$ is in its critical section and a process $k \ne i$ [holds a ticket](has-ticket.md), then $(\mathrm{number}[i], i) < (\mathrm{number}[k], k)$ in [Lamport's order](before.md).

Holding a ticket covers Lamport's "in the bakery" and also the last step of the doorway, after $\mathrm{number}[k]$ is written and before $\mathrm{choosing}[k]$ is reset, so the conclusion is asserted for slightly more processes than in the paper. As for [mutual exclusion](mutual-exclusion.md), the model has atomic registers, which is weaker than Lamport's setting.

## Informally uses

- [The bakery invariant holds in every reachable state](local-inv-of-can-reach.md)

## Sources

- L. Lamport, *A New Solution of Dijkstra's Concurrent Programming Problem*, Communications of the ACM 17(8), August 1974, 453–455: Assertion 2, p. 454.
