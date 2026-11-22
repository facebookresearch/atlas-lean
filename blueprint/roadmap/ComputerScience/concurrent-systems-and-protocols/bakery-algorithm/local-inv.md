# The per-process invariant of the bakery algorithm

Let $s$ be a state of the bakery algorithm for $N$ processes and $i$ a process. The invariant of $i$ in $s$ has five parts:

- $\mathrm{number}[i] > 0$ exactly when $i$ [holds a ticket](has-ticket.md);
- $\mathrm{choosing}[i] = 1$ exactly when $i$ is [in the doorway](in-doorway.md);
- if $i$ is at L2 with index $j$, then $j \le N$ and $i$ is [ahead of](ahead-of.md) every other process with name below $j$;
- if $i$ is at L3 with index $j$, then $j < N$, $i$ is ahead of every other process with name below $j$, and the process named $j$, if different from $i$, is either behind $i$ or [waiting or critical](waiting.md);
- if $i$ is in the critical section, then $i$ is ahead of every other process.

It is the step-by-step form of the case analysis behind Lamport's Assertion 2.

## Sources

- L. Lamport, *A New Solution of Dijkstra's Concurrent Programming Problem*, Communications of the ACM 17(8), August 1974, 453–455: p. 454.
