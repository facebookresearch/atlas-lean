# Sharp state-count thresholds for Dijkstra's K-state token ring

Consider Dijkstra's $K$-state token ring on $n \ge 2$ machines with $K \ge 2$, with legitimate configurations those having exactly one privileged machine. Under a central daemon (one privileged machine moves per step), the ring is self-stabilizing (closure, no deadlock, and convergence of every execution to legitimate configurations after finitely many steps) if and only if $K \ge n - 1$. Under a distributed daemon that may fire any nonempty subset of privileged machines simultaneously, the ring is self-stabilizing if and only if $K \ge n$. In both models legitimate configurations circulate a single token around the ring.

## Proof sketch

Some machine is always privileged. With enough states the bottom machine eventually takes a value held by no other machine, after which the configuration becomes legitimate within a quadratic number of moves. For fewer states, explicit periodic executions cycle forever among illegitimate configurations.

## Depends on

- [Self-stabilization](../../local-distributed-algorithms/self-stabilization.md)

## Proof depends on

- [Self-stabilization of Dijkstra's token ring](../../local-distributed-algorithms/self-stabilization-of-dijkstra-s-k-state-token.md)

## Sources

- Edsger W. Dijkstra, "Self-stabilizing Systems in Spite of Distributed Control", Communications of the ACM, 1974.
- Edsger W. Dijkstra, "Self-stabilization in Spite of Distributed Control", Burroughs Corporation, 1973.
