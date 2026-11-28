# Decomposition theorem for level-k networks representing clusters

Let $\mathcal{X}$ be a finite set of taxa. A **cluster** is a proper subset of $\mathcal{X}$; two clusters $C_1, C_2$ are **compatible** if $C_1 \cap C_2 = \emptyset$, $C_1 \subseteq C_2$ or $C_2 \subseteq C_1$, and **incompatible** otherwise. For a set $\mathcal{C}$ of clusters, the **incompatibility graph** $IG(\mathcal{C})$ has vertex set $\mathcal{C}$ and an edge between every pair of incompatible clusters.

A **rooted phylogenetic network** on $\mathcal{X}$ is a rooted acyclic digraph whose leaves are bijectively labelled by $\mathcal{X}$; nodes of indegree at least $2$ are **reticulations**. The **reticulation number** of a subgraph is $\sum_v (\operatorname{indeg}(v) - 1)$ over its nodes of indegree at least $1$, and a network has **level $k$** if every biconnected component has reticulation number at most $k$. A network $N$ **represents** a cluster $C$ (in the softwired sense) if some tree displayed by $N$, obtained by keeping exactly one incoming edge at every reticulation, has an edge whose descendant leaf set is $C$; $N$ represents $\mathcal{C}$ if it represents every cluster of $\mathcal{C}$. Fix for each $C \in \mathcal{C}$ such an edge $\epsilon(C)$. The network satisfies the **decomposition property** with respect to $\mathcal{C}$ if for all $C_1, C_2 \in \mathcal{C}$, the edges $\epsilon(C_1)$ and $\epsilon(C_2)$ lie in the same biconnected component of $N$ if and only if $C_1$ and $C_2$ lie in the same connected component of $IG(\mathcal{C})$.

**Theorem.** If some level-$k$ network represents $\mathcal{C}$, then some level-$k$ network represents $\mathcal{C}$ and satisfies the decomposition property with respect to $\mathcal{C}$.

The analogous statement with "network with $k$ reticulations" in place of "level-$k$ network" is false.

**Corollary.** A minimum-level network for $\mathcal{C}$ can be assembled by building, for each nontrivial connected component $\mathcal{C}_i$ of $IG(\mathcal{C})$ (after collapsing maximal taxon sets not separated by $\mathcal{C}_i$), a simple network of level at most $k$, and grafting these into the unique tree representing the remaining compatible clusters. For $k \le 2$ the simple networks can be found in polynomial time, so a level-$2$ network representing $\mathcal{C}$ is constructed in polynomial time whenever one exists.

## Depends on

- [Compatible clusters are nested or disjoint](../../splits-compatibility-ultrametrics-and-upgma/compatible-iff-nested-or-disjoint.md)

## Expansion

Given a level-$k$ network $N$ for $\mathcal{C}$, restrict it to the taxa of each connected component $\mathcal{C}_i$, collapsing each maximal unseparated taxon set to one leaf and tidying degree-two and dangling nodes; the result is a simple network of level at most $k$ that still represents the collapsed clusters, because restriction cannot increase the reticulation number of a biconnected component. Clusters in different components of $IG(\mathcal{C})$ are pairwise compatible, so the components sit in a tree-like arrangement given by the compatible "summary" clusters, and replacing the lowest common ancestor of each component's taxa by its simple network yields a level-$k$ network with the decomposition property. A fully compatible cluster set ($IG$ without edges) is represented by a tree, which is the level-$0$ case. Reticulation number does not decompose this way because merging components can share reticulations across them.

## Sources

- L. van Iersel, S. Kelk, R. Rupp, D. Huson, "Phylogenetic networks do not need to be complex: using fewer reticulations to represent conflicting clusters", Bioinformatics 26(12) (2010) i124–i131, Section 2 (definitions), Section 3 (Theorem 1 and the four-step decomposition), Section 4 (Lemmas 1–2 and Theorem 2), <https://doi.org/10.1093/bioinformatics/btq202>, PMCID PMC2881387.
