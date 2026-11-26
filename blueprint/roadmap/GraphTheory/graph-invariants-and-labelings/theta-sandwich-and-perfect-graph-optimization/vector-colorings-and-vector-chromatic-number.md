# Vector colorings and the vector chromatic number

Let $G = (V, E)$ be a finite simple graph with $n \ge 1$ vertices and at least one edge, and let $k > 1$ be real. A *vector $k$-coloring* of $G$ is an assignment of unit vectors $u_v \in \mathbb{R}^n$ to the vertices such that

$$
\langle u_i, u_j \rangle \le -\frac{1}{k - 1} \qquad \text{for every edge } ij \in E ;
$$

it is *strict* if equality holds on every edge. The *vector chromatic number* $\chi_v(G)$ and the *strict vector chromatic number* $\chi_{sv}(G)$ are the smallest real $k$ for which a vector, respectively strict vector, $k$-coloring exists (the minima are attained by compactness). Computing $\chi_v(G)$ is the semidefinite program minimizing $\alpha$ over positive semidefinite matrices $(m_{ij})$ with $m_{ii} = 1$ and $m_{ij} \le \alpha$ on edges, with $\alpha = -1/(k - 1)$ at the optimum.

## Depends on

- [Feasible matrices of the MAX CUT semidefinite program](../../../ComputerScience/approximation-algorithms/goemans-williamson-max-cut-algorithm/sdpfeasible.md)

## Sources

- D. Karger, R. Motwani, M. Sudan, "Approximate Graph Coloring by Semidefinite Programming", Journal of the ACM 45 (1998), arXiv:cs/9812008.
