# Hybridisation number equals the minimum weight of a leaf-added cherry-picking sequence

**Setting.** Let $\mathcal{P}$ be a finite set of rooted phylogenetic $X$-trees (not necessarily binary), $|X| \ge 2$. A rooted phylogenetic network $N$ on $X$ *displays* a phylogenetic $X$-tree $\mathcal T$ if, up to suppressing vertices with in-degree one and out-degree one, some binary refinement of $\mathcal T$ (a binary tree from which $\mathcal T$ is obtained by contracting internal edges) can be obtained from $N$ by deleting edges, leaves not in $X$ and any resulting vertices of out-degree zero; $N$ displays $\mathcal{P}$ if it displays every tree of $\mathcal P$; its hybridisation number is $h(N) = \sum_{v}(d^-(v) - 1)$ over vertices with in-degree $d^-(v) \ge 1$ other than the root. Let $h(\mathcal{P})$ be the minimum of $h(N)$ over all networks displaying $\mathcal{P}$, and $h_{\mathrm{tc}}(\mathcal{P})$ the minimum over tree-child networks (every non-leaf vertex has a child that is not a reticulation).

*Cherry picking.* For an ordered pair $(x,y)$ of leaves, cherry picking $(x,y)$ in a tree $\mathcal{T}$ deletes $x$ (and suppresses its parent if needed) when $\{x,y\}$ is a cherry of $\mathcal{T}$, and leaves $\mathcal{T}$ unchanged otherwise. A sequence $\sigma = (x_1,y_1),\dots,(x_s,y_s),(x_{s+1},-)$ satisfying

$$x_i \notin \{y_{i+1},\dots,y_s\} \quad \text{for all } i \in \{1,\dots,s\}$$

is a **cherry-picking sequence** for $\mathcal{P}$ if picking the pairs in order, simultaneously in every tree, reduces every tree to the single vertex $x_{s+1}$. Its weight is $w(\sigma) = s + 1 - |X|$, and $s(\mathcal{P})$ is the minimum weight. *Attaching* a new leaf $z$ to a tree means subdividing an edge and hanging $z$ there, adding $z$ above the root, or joining $z$ to an existing interior vertex. A **leaf-added cherry-picking sequence** for $\mathcal{P}$ is a cherry-picking sequence of some set obtained from $\mathcal{P}$ by attaching a set $Z$ of auxiliary leaves ($Z \cap X = \emptyset$) to each tree; its weight is $s + 1 - (|X| + |Z|)$, and $s_+(\mathcal{P})$ is the minimum weight.

**Theorem.** For every finite set $\mathcal{P}$ of phylogenetic $X$-trees,

$$h_{\mathrm{tc}}(\mathcal{P}) = s(\mathcal{P}), \qquad h(\mathcal{P}) = s_+(\mathcal{P}).$$

Moreover there is a set $Z$ of auxiliary leaves with $|Z| \le h_{\mathrm{tc}}(\mathcal{P})$ and a collection $\mathcal{P}_Z$ obtained from $\mathcal{P}$ by attaching $Z$ such that $h(\mathcal{P}) = h_{\mathrm{tc}}(\mathcal{P}_Z)$: adding few leaves turns the general hybridisation problem into the tree-child one. The inequality $s_+(\mathcal{P}) \le s(\mathcal{P})$ can be strict.

**Complexity.** Deciding whether $h_{\mathrm{tc}}(\mathcal{P}) \le k$ is NP-complete; nevertheless every set $\mathcal{P}$ is displayed by some tree-child network, since for each $n \ge 2$ there is a tree-child network on $n$ leaves displaying all binary phylogenetic trees on those leaves.

## Expansion

Reading a cherry-picking sequence backwards builds a network: the last element is the root leaf, and each pair $(x_i,y_i)$ either inserts $x_i$ as a sibling of $y_i$ (first occurrence of $x_i$ in the reversed order) or adds a reticulation edge from the pendant edge of $y_i$ into the existing pendant edge of $x_i$. Condition (P) guarantees the result is tree-child, every tree of $\mathcal{P}$ is displayed because each step undoes a cherry pick, and the number of reticulation edges is $s + 1 - |X|$. Conversely, a tree-child network displaying $\mathcal{P}$ always has a cherry or reticulated cherry whose reduction yields such a sequence. For arbitrary networks the obstacle is that a reticulation may have no leaf "beneath" it to pick; attaching an auxiliary leaf below each problematic reticulation makes the network tree-child without changing its hybridisation number, and at most $h_{\mathrm{tc}}(\mathcal{P})$ such leaves are needed. For two binary trees $h(\mathcal{P})$ equals the size of a maximum acyclic agreement forest minus one, but no agreement-forest characterisation is known for three or more trees; the leaf-added sequences supply one for any number of (non-binary) trees.

## Sources

- Simone Linz and Charles Semple, "Attaching leaves and picking cherries to characterise the hybridisation number for a set of phylogenies", arXiv:1712.04131 (2017), Section 1 (definition of display via binary refinements), Theorems 1.2 and 1.3, Corollary 1.4, Theorems 2.1 and 2.2, Theorem 4.2, <https://doi.org/10.48550/arXiv.1712.04131>. Published version: Advances in Applied Mathematics, 105:102-129, 2019, <https://doi.org/10.1016/j.aam.2019.01.004>.
