# Exploration trees

Let $(X_{h,i}, x_{h,i})$ be a [hierarchical partition](hierarchical-partition.md) of a set $\mathcal X$ with branching
factor $K$. For a set $T$ of nodes, a *leaf* of $T$ is a node of $T$ none of whose children belongs to $T$, and
*expanding* a leaf $(h, i)$ of $T$ means replacing $T$ by $T \cup \{(h + 1, Ki + k) : 0 \le k \le K - 1\}$, the set
$T$ with the $K$ children of $(h, i)$ added. An *exploration tree* is a set of nodes obtained from $\{(0, 0)\}$ by
finitely many expansions of leaves. Its nodes that are not leaves are its *expanded* nodes, and its *depth* is the
largest depth of its nodes.

An expansion turns a leaf into an expanded node and adds $K$ new leaves, so an exploration tree obtained by $t$
expansions has $t$ expanded nodes; it is finite, and a node of largest depth is a leaf, so every exploration tree has a
leaf.

## Sources

- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Section 3.1.
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.3.

## Depends on

- [Hierarchical partition](hierarchical-partition.md)
