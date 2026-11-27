# Stable phylogenetic networks and their characterization

**Definitions.** A *phylogenetic network* $N$ on a finite leaf set $X$ ($|X| \ge 2$) is a rooted, connected directed acyclic graph without parallel arcs whose leaves are bijectively labelled by $X$; *tree vertices* have in-degree at most one and *reticulation vertices* in-degree at least two, with $\mathrm{Ret}(N)$ the set of reticulations. A *MUL-tree* is a rooted tree whose leaves are labelled by $X$ with labels possibly repeated. The *unfolding* $U(N)$ is the MUL-tree whose vertices are the directed paths in $N$ starting at the root, a path being the child of its one-arc-shorter prefix, with leaves labelled by the leaf at the path's end. The *folding* (fold-up) $F(T)$ of a MUL-tree $T$ identifies vertices whose pendant sub-MUL-trees are isomorphic, producing a rooted DAG that exhibits $T$; $U(F(T)) \cong T$. A network is

- *stable* if $F(U(N)) \cong N$;
- *semi-resolved* if every tree vertex has out-degree $2$ (true of $F(T)$ whenever $T$ is binary);
- *compressed* if the child of each reticulation vertex is a tree vertex;
- *irreducible* if it has no *identifiable* pair, i.e. no distinct tree vertices $v, w$ reached by root paths $\gamma_v, \gamma_w$ whose sub-MUL-trees $T(\gamma_v), T(\gamma_w)$ of $U(N)$ are isomorphic.

**Proposition.** For a binary MUL-tree $T$ on $X$, $F(T)$ is a phylogenetic network iff no two distinct vertices of $T$ with a common parent have isomorphic pendant sub-MUL-trees.

**Theorem.** For a semi-resolved phylogenetic network $N$ the following are equivalent:

1. $N$ is stable;
2. $N$ is compressed and irreducible;
3. $N$ is compressed and no two distinct tree vertices $v, w$ have the same set of children, $ch(v) = ch(w)$.

**Corollary.** Every binary, compressed tree-sibling network (each reticulation has a sibling that is a tree vertex) is stable; in particular this applies to binary compressed tree-child networks. Conversely there are semi-resolved compressed tree-sibling networks that are not stable, binary stable networks that are not tree-sibling, and non-binary tree-child networks that are not stable.

## Expansion

If two siblings in $T$ have isomorphic subtrees, folding identifies them and creates parallel arcs, which is why the proposition's condition is exactly what makes $F(T)$ a network. In the theorem, a reticulation whose child is again a reticulation is collapsed by unfolding and folding (the order of consecutive hybridizations is not recoverable), so stability forces compression; identifiable tree vertices produce isomorphic subtrees in $U(N)$ that folding would merge, so stability forces irreducibility. For (2) $\Rightarrow$ (3): two tree vertices with equal child sets must both have only reticulation children, which compression and semi-resolution turn into an identifiable pair. In a tree-sibling network, two tree vertices sharing all children would make those children reticulations with no tree-vertex sibling, so condition (3) holds. Since $F(T)$ has the minimum number of reticulations among networks exhibiting a binary $T$, stable networks are canonical minimal representatives of their MUL-trees.

## Sources

- K. T. Huber, V. Moulton, M. Steel, T. Wu, "Folding and unfolding phylogenetic trees and networks", Journal of Mathematical Biology (2016), Sections 2–4, definitions of $U$, $F$, compressed and irreducible networks, Proposition 1, Theorem 1 and Corollary 1 (Figure 4). <https://doi.org/10.1007/s00285-016-0993-5> (PMC5061860).
