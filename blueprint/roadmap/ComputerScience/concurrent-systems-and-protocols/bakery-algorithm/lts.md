# The bakery algorithm as a labelled transition system

The bakery algorithm for $N$ processes is the labelled transition system whose states are the [states of the algorithm](state.md) and whose labels are the processes: $s \xrightarrow{p} s'$ when $s'$ is obtained from $s$ by [updating](set-local.md) the program counter, $\mathrm{choosing}[p]$ and $\mathrm{number}[p]$ to the values of some [atomic action](local-step.md) of $p$ in $s$.

## Sources

- L. Lamport, *A New Solution of Dijkstra's Concurrent Programming Problem*, Communications of the ACM 17(8), August 1974, 453–455: p. 454.
