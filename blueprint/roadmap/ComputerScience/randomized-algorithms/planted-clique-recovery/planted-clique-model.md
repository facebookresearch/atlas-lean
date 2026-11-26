# The planted clique model and recovery

For $n$ and a set $S \subseteq [n]$ with $|S| = k$, the **planted graph** $G(n, 1/2, S)$ is obtained by including every pair inside $S$ as an edge and every other pair independently with probability $1/2$. A **recovery algorithm** receives the graph and the target size $k$ (but not $S$) and must output $S$. Its **failure probability** at $S$ is the probability over the edge coins that it outputs a set other than $S$. The **signed adjacency matrix** has entries $+1$ for edges and $-1$ for non-edges off the diagonal; it equals the rank-one signal $\mathbf{1}_S \mathbf{1}_S^\top$ plus a centered noise matrix plus a diagonal correction of operator norm at most $1$.

## Depends on

- [Hardness of the planted clique problem](../../../TheoryOfComputation/randomized-and-quantum-complexity/hardness-of-the-planted-clique-problem.md)

## Sources

- N. Alon, M. Krivelevich and B. Sudakov, "Finding a Large Hidden Clique in a Random Graph", Random Structures & Algorithms 13(3-4), 1998.
- L. Kučera, "Expected Complexity of Graph Partitioning Problems", Discrete Applied Mathematics 57(2-3), 1995.
