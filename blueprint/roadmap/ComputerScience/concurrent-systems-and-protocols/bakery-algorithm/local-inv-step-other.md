# A step of another process preserves a process's bakery invariant

Let $s$ be a state of the bakery algorithm and $i \ne p$ processes. If process $i$ satisfies the [per-process invariant](local-inv.md) in $s$ and process $p$ takes one [atomic action](local-step.md), then $i$ still satisfies it in the resulting state. The values of $i$ do not change; the only work is to check that $p$, whatever it does, stays [behind $i$](ahead-of.md) when it was behind $i$, and that a process $p$ that $i$ is about to read at L3 is still either behind $i$ or waiting.

## Sources

- L. Lamport, *A New Solution of Dijkstra's Concurrent Programming Problem*, Communications of the ACM 17(8), August 1974, 453–455: Assertions 1 and 2, p. 454.
