# Every circulation is a combination of fundamental tree cycles

Let $T$ be a spanning tree of $G$ and $\mathbf{\Delta}$ a circulation on $G$. Then

$$
\mathbf{\Delta} = \sum_{e \in E \setminus T} \mathbf{\Delta}_e\, \boldsymbol{\chi}^T_e.
$$

## Proof sketch

The difference $\mathbf{\Delta} - \sum_{e \notin T}\mathbf{\Delta}_e\boldsymbol{\chi}^T_e$ is a circulation because each term is, and it vanishes on every off-tree edge since $\boldsymbol{\chi}^T_e$ is $1$ on $e$ and $0$ on other off-tree edges. A circulation supported on the edges of a forest is zero, because a leaf edge of its support would carry nonzero net flow into a leaf.

## Depends on

- [Fundamental tree cycles as circulations](fundamental-tree-cycle-circulation.md)

## Proof depends on

- [Oriented incidence matrix of a multigraph](../../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
