# Holding a ticket

A process of the bakery algorithm holds a ticket when its program counter is about to reset $\mathrm{choosing}$, at statement L2 or L3 of the loop (for any index), or in the critical section: it has written its ticket $\mathrm{number}[i]$ and has not left its critical section or failed. Lamport's "in the bakery" starts one step later, when $\mathrm{choosing}[i]$ is reset.

## Sources

- L. Lamport, *A New Solution of Dijkstra's Concurrent Programming Problem*, Communications of the ACM 17(8), August 1974, 453–455: p. 454.
