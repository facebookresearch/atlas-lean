# Orchard networks and cherry picking

A (directed) **phylogenetic network** on a finite taxon set $X$ is a directed acyclic graph whose nodes are a root (indegree $0$, outdegree $1$), tree nodes (indegree $1$, outdegree $\ge2$), reticulations (indegree $\ge2$, outdegree $1$) and leaves (indegree $1$, outdegree $0$), with the leaves bijectively labelled by $X$. It is **binary** if every tree node and reticulation has total degree $3$. The reticulation number $r(N)$ is the number of reticulation arcs minus the number of reticulations.

An ordered pair $(x,y)$ of distinct leaves, $x\ne y$, is a **cherry** if $x$ and $y$ have a common parent, and a **reticulated cherry** if the parent $p_x$ of $x$ is a reticulation and $p_x$ and $y$ have a common parent; either is a **reducible pair**. **Reducing** $(x,y)$ means: for a cherry, delete $x$; for a reticulated cherry, delete the arc $(p_y,p_x)$; in both cases then suppress nodes of indegree $1$ and outdegree $1$. The result $N_{(x,y)}$ is again a network on a subset of $X$.

A network is **orchard** if some sequence $S$ of ordered pairs reduces it, by successive reductions, to a tree with a single leaf. Picking any reducible pair of an orchard network yields an orchard network, so the order of reductions does not matter for membership.

## Expansion

A cherry reduction removes one leaf; a reticulated-cherry reduction removes one reticulation arc and keeps the leaf set. A binary orchard network on $n$ leaves with $k$ reticulations is therefore reduced by exactly $n-1+k$ pairs, and reversing a cherry-picking sequence reconstructs the network by attaching pairs. Tree-child networks, where every non-leaf node has a child that is a tree node or leaf, are orchard; orchard networks need not be tree-child.

## Sources

- L. van Iersel, R. Janssen, M. Jones, Y. Murakami, *Orchard networks are trees with additional horizontal arcs*, Bulletin of Mathematical Biology 84 (2022), <https://doi.org/10.1007/s11538-022-01037-z> (PMCID: PMC9213324). Section 2, Definitions 1–4; the order-independence of reductions is quoted there from Janssen and Murakami (2021) and Erdős et al. (2019).
