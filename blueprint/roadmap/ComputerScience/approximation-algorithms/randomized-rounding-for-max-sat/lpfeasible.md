# Feasible solutions of the MAX SAT linear relaxation

For clauses $C_1, \ldots, C_m$, a pair $(y, z)$ is feasible for (LP) when $0 \le y_i \le 1$ for
every variable, and $0 \le z_j \le 1$ and $z_j$ is at most the [clause bound](lp-clause-bound.md) of
$C_j$ at $y$ for every clause: the sum over the literals of $C_j$, with multiplicity, of $y_i$ for a
literal $x_i$ and $1 - y_i$ for a literal $\bar x_i$, which for distinct variables is
$\sum_{i \in P_j} y_i + \sum_{i \in N_j}(1 - y_i)$. The objective is $\sum_j w_j z_j$. The bound $0 \le y_i \le 1$ is imposed on every variable
index $i \in \mathbb{N}$, which costs nothing since unused variables can be set to $0$.

## Background

- [Linear programming](../../../Geometry/convex-geometry/linear-programming/README.md): (LP) is a
  linear program; Goemans and Williamson solve it in strongly polynomial time with Tardos'
  algorithm.

## Sources

- M. X. Goemans and D. P. Williamson, "New 3/4-approximation algorithms for the maximum satisfiability problem", *SIAM J. Discrete Math.* 7(4) (1994), 656–666 (journal version), §3.
