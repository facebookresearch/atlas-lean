# Planted clique model, search and detection problems

For $n \ge 1$ and a set $S \subseteq \{1, \dots, n\}$, the *planted-clique graph* $G(n, 1/2, S)$ includes each pair $\{u, v\}$ independently with probability $1/2$, except that every pair inside $S$ is an edge. Its *noise matrix* is the symmetric $n \times n$ matrix that is $0$ on the diagonal and inside $S \times S$, and otherwise $+1$ for an edge and $-1$ for a non-edge. In the *planted clique search problem*, a hidden $k$-set $S$ is drawn from a prior (usually uniform over $k$-subsets), the graph is drawn given $S$, and an algorithm that sees only the graph (and $k$) succeeds if it outputs exactly $S$; the *detection problem* distinguishes this graph from $G(n, 1/2)$.

## Depends on

- [Hardness of the planted clique problem](../../../TheoryOfComputation/randomized-and-quantum-complexity/hardness-of-the-planted-clique-problem.md)

## Sources

- Noga Alon, Michael Krivelevich and Benny Sudakov, "Finding a large hidden clique in a random graph", Random Structures & Algorithms 13(3-4), 1998.
