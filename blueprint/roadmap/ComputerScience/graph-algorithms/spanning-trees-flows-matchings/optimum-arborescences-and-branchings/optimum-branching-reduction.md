# Optimum branchings by the super-root reduction

Let $G$ be a digraph with arc weights $w$. Add a new vertex $\rho$, an arc of cost $0$ from every original vertex to $\rho$, and give each original arc $u \to v$ the cost $-w(v, u)$ in the reversed direction. Then minimum-cost spanning in-arborescences rooted at $\rho$ of this instance correspond bijectively, with cost equal to minus weight, to branchings of $G$, so Chu-Liu/Edmonds computes a **maximum-weight branching** of $G$; running it on $-w$ gives a minimum-weight branching. The reduction always has a spanning in-arborescence, so it never fails.

## Proof sketch

Every vertex either has a parent in the branching or points to $\rho$; acyclicity of the branching is reachability of $\rho$.

## Depends on

- [Spanning arborescences and branchings](spanning-arborescences-and-branchings.md)
- [The Chu-Liu/Edmonds algorithm](chu-liu-edmonds-algorithm.md)

## Proof depends on

- [Correctness and optimality of Chu-Liu/Edmonds](chu-liu-edmonds-correctness.md)

## Sources

- J. Edmonds, "Optimum Branchings", Journal of Research of the National Bureau of Standards, Section B 71B(4), 1967.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
