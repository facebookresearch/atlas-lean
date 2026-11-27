# Karp-Bax inclusion-exclusion formula for Hamiltonian paths

Let $G$ be a directed graph on vertex set $V$ with $|V| = n$. For $S \subseteq V$ let $w(S)$ be the number of walks $(v_1, \dots, v_n)$ of $n$ vertices (not necessarily distinct) with all $v_i \in S$ and $v_i v_{i+1} \in E(G)$. Then the number of Hamiltonian paths of $G$ equals

$$
\sum_{S \subseteq V} (-1)^{n - |S|}\, w(S).
$$

Moreover $w(S) = \mathbf{1}^\top (A_S)^{n-1} \mathbf{1}$ for the adjacency matrix $A_S$ of $G[S]$, computable with $O(n^3)$ arithmetic operations keeping one length-$n$ walk-count vector.

## Proof sketch

A walk of $n$ vertices is a Hamiltonian path exactly when it visits every vertex; inclusion-exclusion over the set of avoided vertices counts walks visiting all of $V$.

## Depends on

- [HAMILTONIAN PATH (UNDIRECTED) as a decision problem](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/undirected-hamiltonian-path/hamiltonian-path-undirected-dec.md)

## Sources

- R. M. Karp, "Dynamic Programming Meets the Principle of Inclusion and Exclusion", Operations Research Letters 1(2), 1982.
- E. T. Bax, "Inclusion and Exclusion Algorithm for the Hamiltonian Path Problem", Information Processing Letters 47(4), 1993.
- F. V. Fomin and D. Kratsch, "Exact Exponential Algorithms", Springer, 2010.
