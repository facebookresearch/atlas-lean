# Totally unimodular systems have integral vertices

If $A$ is a totally unimodular matrix and $b$ is integral, then every vertex of $\{x : Ax \le b\}$ is integral, and any finite optimum of a linear program over it is attained at an integral point. If moreover $c$ is integral and $\max\{c^{\mathsf T}x : Ax \le b\}$ is finite, then both sides of the duality equation $\max\{c^{\mathsf T}x : Ax \le b\} = \min\{y^{\mathsf T}b : y \ge 0, y^{\mathsf T}A = c^{\mathsf T}\}$ have integral optimal solutions. Since appending $-I$ preserves total unimodularity, this covers $\{x : Ax \le b, x \ge 0\}$. Not every optimal solution need be integral. The incidence matrix of a directed graph (a loop gives a zero column) is totally unimodular, and a loopless undirected graph is bipartite if and only if its unsigned incidence matrix is totally unimodular.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- A nonsingular square system with totally unimodular matrix and integral right-hand side has an integral solution (Cramer's rule).
- Vertices of $\{x : Ax \le b\}$ are the points whose tight rows have rank $n$.

## Sources

- A. Schrijver, *A Course in Combinatorial Optimization*, lecture notes, CWI and University of Amsterdam, 2017, <https://homepages.cwi.nl/~lex/files/dict.pdf>, §8.2, Theorem 8.1 and Corollaries 8.1a–8.1b
- A. Schrijver, *A Course in Combinatorial Optimization*, lecture notes, CWI and University of Amsterdam, 2017, <https://homepages.cwi.nl/~lex/files/dict.pdf>, §8.3, Theorem 8.3, and §8.4, Theorem 8.4
