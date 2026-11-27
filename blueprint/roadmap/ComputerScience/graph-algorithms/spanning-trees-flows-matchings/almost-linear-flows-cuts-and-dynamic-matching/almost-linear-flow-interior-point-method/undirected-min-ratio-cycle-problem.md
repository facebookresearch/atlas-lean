# Undirected minimum-ratio cycle problem with gradients and lengths

Let $G = (V, E)$ be a directed graph with incidence matrix $\mathbf{B}$, gradients $\mathbf{g} \in \mathbb{R}^E$ and lengths $\boldsymbol{\ell} \in \mathbb{R}^E_{>0}$, and $\mathbf{L} = \mathrm{diag}(\boldsymbol{\ell})$. The minimum-ratio cycle problem asks for a nonzero circulation $\mathbf{\Delta}$, that is $\mathbf{B}^{\top}\mathbf{\Delta} = \mathbf{0}$, minimizing

$$
\frac{\mathbf{g}^{\top}\mathbf{\Delta}}{\|\mathbf{L}\mathbf{\Delta}\|_1}.
$$

The problem is undirected: coordinates of $\mathbf{\Delta}$ may have either sign, so the optimum is at most $0$ (replace $\mathbf{\Delta}$ by $-\mathbf{\Delta}$). For $\kappa \in (0, 1]$, a circulation $\mathbf{\Delta}$ is a $\kappa$-approximate minimum-ratio cycle if its ratio is at most $\kappa$ times the optimum. Minimizing a ratio of a linear objective over cycles generalizes the minimum cycle mean, which is the case of unit lengths restricted to directed cycles.

## Depends on

- [Oriented incidence matrix of a multigraph](../../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
