# Update by one process

Let $s$ be a state of the bakery algorithm, $p$ a process, $c$ a program counter, $b \in \{0, 1\}$ and $n \in \mathbb{N}$. The update of $s$ by $p$ with $(c, b, n)$ is the state in which the program counter of $p$ is $c$, $\mathrm{choosing}[p] = b$ and $\mathrm{number}[p] = n$, and everything else is as in $s$.

## Sources

- L. Lamport, *A New Solution of Dijkstra's Concurrent Programming Problem*, Communications of the ACM 17(8), August 1974, 453–455: p. 454.
