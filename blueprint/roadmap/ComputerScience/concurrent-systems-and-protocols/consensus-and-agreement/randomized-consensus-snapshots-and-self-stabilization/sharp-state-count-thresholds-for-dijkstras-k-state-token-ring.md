# Sharp state-count thresholds for Dijkstra's K-state token ring

Consider Dijkstra's $K$-state token ring on $n \ge 2$ machines with $K \ge 2$, with legitimate configurations those having exactly one privileged machine. Under a central daemon (one privileged machine moves per step), the ring is self-stabilizing (closure, no deadlock, and convergence of every execution to legitimate configurations after finitely many steps) if and only if $K \ge n - 1$: for $n \ge 3$ the ring stabilizes even when $K = n - 1$ (Fokkink, Hoepman and Pang, Theorem 1), and for $K < n - 1$ an explicit execution cycles forever among illegitimate configurations (Fokkink, Hoepman and Pang, §4; Dijkstra, EWD391, p. 5). Legitimate configurations circulate a single token around the ring.

## Proof sketch

Some machine is always privileged. With enough states the bottom machine eventually takes a value held by no other machine, after which the configuration becomes legitimate within a quadratic number of moves. For fewer states, explicit periodic executions cycle forever among illegitimate configurations: with $K = n - 2$ and counter values $0, 1, \dots, n - 3, 0, 1$ around the ring, firing the machines from the last one backwards to the bottom machine reaches, after one move of each machine, a configuration symmetric to the initial one (counter values shifted modulo $K$), with as many privileged machines. For two machines, $K \ge 2$ suffices. Under a distributed daemon that may fire any nonempty subset of privileged machines at once, the corresponding threshold is $K \ge n$: $K \ge n$ suffices under the unfair distributed daemon, and for $K = n - 1$ the synchronous daemon has a non-stabilizing execution (Altisen, Devismes, Dubois and Petit, Introduction to Distributed Self-Stabilizing Algorithms, Morgan & Claypool, 2019, as summarized by Khoualdia, Cherif, Devismes and Robert, CP 2026, §2).

## Depends on

- [Self-stabilization](../../local-distributed-algorithms/self-stabilization.md)

## Proof depends on

- [Self-stabilization of Dijkstra's token ring](../../local-distributed-algorithms/self-stabilization-of-dijkstra-s-k-state-token.md)

## Sources

- Wan Fokkink, Jaap-Henk Hoepman and Jun Pang, "A Note on K-State Self-Stabilization in a Ring with K = N", Nordic Journal of Computing, 2005, Theorem 1 and §4.
- Edsger W. Dijkstra, "Self-stabilizing Systems in Spite of Distributed Control", Communications of the ACM, 1974.
- Edsger W. Dijkstra, "Self-stabilization in Spite of Distributed Control", Burroughs Corporation, 1973.
