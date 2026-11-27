# Undirected minimum-ratio cycle problem with gradients and lengths

Let $G = (V, E)$ be a directed graph with incidence matrix $\mathbf{B}$, gradients $\mathbf{g} \in \mathbb{R}^E$ and lengths $\boldsymbol{\ell} \in \mathbb{R}^E_{>0}$, and $\mathbf{L} = \mathrm{diag}(\boldsymbol{\ell})$. When $G$ has a nonzero circulation, that is, when its underlying undirected multigraph contains a cycle (a loop or a pair of parallel edges counts), the minimum-ratio cycle problem asks for a nonzero circulation $\mathbf{\Delta}$, that is $\mathbf{B}^{\top}\mathbf{\Delta} = \mathbf{0}$, minimizing

$$
\frac{\mathbf{g}^{\top}\mathbf{\Delta}}{\|\mathbf{L}\mathbf{\Delta}\|_1}.
$$

When $G$ is a forest its only circulation is $\mathbf{0}$, the ratio is undefined, and the answer is that no cycle exists. The problem is undirected: coordinates of $\mathbf{\Delta}$ may have either sign, so the optimum is at most $0$ (replace $\mathbf{\Delta}$ by $-\mathbf{\Delta}$); it is attained, since the ratio is invariant under positive scaling and the circulations with $\|\mathbf{L}\mathbf{\Delta}\|_1 = 1$ form a compact set. For $\kappa \in (0, 1]$, a circulation $\mathbf{\Delta}$ is a $\kappa$-approximate minimum-ratio cycle if its ratio is at most $\kappa$ times the optimum. It is an undirected analogue of the minimum cycle mean problem, which minimizes the average cost of a directed cycle.

## Depends on

- [Oriented incidence matrix of a multigraph](../../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
