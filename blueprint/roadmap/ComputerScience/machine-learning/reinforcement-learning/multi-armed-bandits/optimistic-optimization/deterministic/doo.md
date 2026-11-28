# Deterministic optimistic optimization (DOO)

Let $(X_{h,i}, x_{h,i})$ be a [hierarchical partition](../hierarchical-partition.md) of a set $\mathcal X$ with
branching factor $K$, let $f \colon \mathcal X \to \mathbb{R}$, and let $\delta \colon \mathbb{N} \to \mathbb{R}$. The
*b-value* of a node $(h, i)$ is

$$
b_{h,i} = f(x_{h,i}) + \delta(h).
$$

DOO with budget $n \in \mathbb{N}$ builds [exploration trees](../exploration-trees.md) $T_0 \subseteq T_1 \subseteq
\dots \subseteq T_n$: $T_0 = \{(0, 0)\}$ and, for $t = 1, \dots, n$, $T_t$ is obtained from $T_{t-1}$ by expanding a
leaf of $T_{t-1}$ whose b-value is the largest among the leaves of $T_{t-1}$. It returns $x(n) = x_{h,i}$ for a node
$(h, i) \in T_n$ whose value $f(x_{h,i})$ is the largest among the nodes of $T_n$. Ties are broken arbitrarily: a
*run* of DOO with budget $n$ is any sequence of trees and returned point that follow these rules, and the results on
DOO hold for every run.

DOO uses $f$ only at the centers of the nodes of its trees: the root's center, and the centers of the $K$ children
of each expanded node, so $Kn + 1$ evaluations in all (the sources count $Kn$, leaving out the root). It is
optimistic: with $\delta$ bounding the diameters of the cells for a semi-metric under which $f$ is locally smooth
around a maximizer $x^*$, the b-value of a cell that contains $x^*$ is at least $\max f$, and DOO expands a leaf whose
cell may contain $x^*$.

The sources start from $T_1 = \{(0, 0)\}$ and return the best node of $T_n$ after rounds $t = 1, \dots, n$; here
$T_t$ is the tree after $t$ expansions, and $n$ is the number of expansions, as in the analysis of the sources.

## Sources

- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Section 3.1 and Figure 1.
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.3 and Figure 3.6.

## Depends on

- [Hierarchical partition](../hierarchical-partition.md)
- [Exploration trees](../exploration-trees.md)
