# The bakery invariant holds in every reachable state

In every state reachable from the [initial state](init.md) of the [bakery algorithm](lts.md), every process satisfies the [per-process invariant](local-inv.md). It holds initially, a step of another process preserves it, and a step of the process itself preserves it given the invariants of all processes; induction on the number of steps extends this to every reachable state.

## Informally uses

- [A step of another process preserves a process's bakery invariant](local-inv-step-other.md)
- [A step of a process preserves its own bakery invariant](local-inv-step-self.md)

## Sources

- L. Lamport, *A New Solution of Dijkstra's Concurrent Programming Problem*, Communications of the ACM 17(8), August 1974, 453–455: p. 454.
