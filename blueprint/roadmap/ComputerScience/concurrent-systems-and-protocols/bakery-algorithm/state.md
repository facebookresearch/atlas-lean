# State of the bakery algorithm

A state of the bakery algorithm for $N$ processes consists of a [program counter](program-counter.md) for each process and the two shared arrays: $\mathrm{choosing}$, a Boolean per process (Lamport's $0$ or $1$), and $\mathrm{number}$, a natural-number ticket per process.

## Related topics

- [State of the two-process bakery algorithm](../two-process-bakery-algorithm/state.md): the separate model of the two-process case, with its own program counters.

## Sources

- L. Lamport, *A New Solution of Dijkstra's Concurrent Programming Problem*, Communications of the ACM 17(8), August 1974, 453–455: p. 454.
