# Treewidth as the minimum width of an agreeing rooted tree

**Definitions.** Let $G$ be an undirected graph. A rooted tree $\Gamma$ on the vertex set $V(G)$ *agrees with* $G$ if for every edge $uv \in E(G)$ one of $u, v$ is an ancestor of the other in $\Gamma$ (write $w \le_\Gamma v$ when $w$ is in the subtree of $v$). For $v \in V(G)$ let

$$YW^\Gamma_v = \{u >_\Gamma v : \exists\, w \le_\Gamma v \text{ with } uw \in E(G)\}, \qquad yw^\Gamma_v = |YW^\Gamma_v|,$$

the strict ancestors of $v$ adjacent to some vertex of the subtree of $v$. Put $yw(\Gamma) = \max_v yw^\Gamma_v$ and $yw(G) = \min_\Gamma yw(\Gamma)$ over agreeing trees.

**Proposition.** $yw(G) = tw(G)$, the treewidth of $G$. Moreover, from a tree decomposition $(T, B)$ of $G$ one can compute in linear time an agreeing tree $\Gamma$ with $yw(\Gamma) = tw(T, B)$, the width of the decomposition.

## Depends on

- [Tree-decomposition](../../../../GraphTheory/planar-graphs-and-minors/tree-width/tree-decomposition.md)
- [Tree-width at most $k$](../../../../GraphTheory/planar-graphs-and-minors/tree-width/has-treewidth-at-most.md)

## Expansion

Given an agreeing tree, the bags $\{v\} \cup YW^\Gamma_v$ arranged along $\Gamma$ form a tree decomposition of width $yw(\Gamma)$: every edge joins a vertex to an ancestor, so it lies in the bag of the lower endpoint, and the vertices whose bags contain a fixed $u$ form a connected set of descendants of $u$. Conversely, eliminating vertices along a nice tree decomposition (forget nodes give the order) yields an agreeing tree whose sets $YW_v$ sit inside bags. The formulation suits networks because a dynamic program can process the network's vertices bottom-up along $\Gamma$, keeping state only for the at most $yw(\Gamma)$ "open" ancestors.

## Sources

- C. Scornavacca and M. Weller, "Treewidth-based algorithms for the small parsimony problem on networks", *Algorithms for Molecular Biology* (2022), Definitions 1–2, Lemmas 1–3 and Proposition 1. <https://doi.org/10.1186/s13015-022-00216-w> (PMC9392953)
