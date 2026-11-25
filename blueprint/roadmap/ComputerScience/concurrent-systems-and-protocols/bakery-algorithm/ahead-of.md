# One bakery process ahead of another

Let $s$ be a state of the bakery algorithm for $N$ processes and $i$, $k$ processes. Process $i$ is ahead of process $k$ in $s$ if, according to the program counter of $k$:

- $k$ is in its noncritical section; or
- $k$ is in the doorway reading tickets, with set $U$ of processes still to read and running maximum $m$, and $i \in U$ or $\mathrm{number}[i] \le m$; or
- $k$ is about to write the ticket $1 + m$ and $\mathrm{number}[i] \le m$; or
- $k$ [holds a ticket](has-ticket.md) and $(\mathrm{number}[i], i) < (\mathrm{number}[k], k)$ in [Lamport's order](before.md).

For $k \ne i$, the condition is preserved by every [atomic action](local-step.md) of $k$: whatever $k$ does next, it does not overtake $i$.

## Sources

- L. Lamport, *A New Solution of Dijkstra's Concurrent Programming Problem*, Communications of the ACM 17(8), August 1974, 453–455: p. 454.
