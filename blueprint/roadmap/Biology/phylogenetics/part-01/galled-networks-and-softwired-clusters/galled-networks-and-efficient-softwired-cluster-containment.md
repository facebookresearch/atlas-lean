# Galled networks and efficient softwired cluster containment

**Definitions.** Let $\mathcal X$ be a finite set of taxa. A *cluster* is a subset $C \subset \mathcal X$ with $\emptyset \ne C \ne \mathcal X$. In a rooted phylogenetic network $N$ (a rooted DAG with leaves labelled by $\mathcal X$), nodes of in-degree at most one are *tree nodes*, others are *reticulations*; edges into reticulations are *reticulate edges*, all others *tree edges*. A *switching* chooses one incoming edge at every reticulation. $N$ represents a set of clusters $\mathcal C$

- in the *hardwired* sense if there is a bijection between $\mathcal C$ and the tree edges of $N$ such that the leaves below each edge are exactly its cluster;
- in the *softwired* sense if for every $C \in \mathcal C$ there are a tree edge $e$ and a switching such that the leaves reachable below $e$ under that switching are exactly $C$.

$N$ is a *galled network* if for every reticulation $r$ and every pair of reticulate edges $p, q$ into $r$ there is a *tree cycle*: an undirected cycle through $p$ then $q$ that otherwise uses only tree edges.

**Facts.**

1. Every reticulation $r$ of a galled network is a cut node separating the descendants of $r$ from the other nodes.
2. *Existence.* Every set of clusters on $\mathcal X$ is represented in the softwired sense by some galled network (unlike galled trees or level-$k$ networks).
3. *Cluster containment (efficient).* For a tree edge $e = (v, w)$ let $L_e$ be the taxa reachable from $w$ by tree edges only, $R_e$ the reticulations reachable from $w$ by tree edges followed by one reticulate edge, and $Y_r$ the taxa below $r$. Each $Y_r$ with all parents of $r$ below $w$ is forced into every cluster represented by $e$; every other $r \in R_e$ is optional (all of $Y_r$ or none of it). Hence $e$ represents $C$ iff $C$ equals $L_e$ together with the forced sets and the union of $Y_r$ over some subset of the optional reticulations, which is checked in polynomial time.

**Decomposition.** Clusters $A, B$ are compatible if disjoint or nested; a set of clusters is represented by a rooted tree iff it is pairwise compatible. The incompatibility graph has the clusters as nodes and edges between incompatible pairs. The method restricts to *decomposable* representations, assembled from separate networks for the connected components of this graph; for these, each component (with taxa not separated by any of its clusters collapsed) is solved independently. This is a restriction, not a theorem: a network with the fewest reticulations need not be decomposable (Huson et al., Fig. 3, give a cluster set needing four reticulations in any decomposable network but three in a non-decomposable one).

## Expansion

The cut-node property follows from the tree cycles: removing $r$ leaves its descendants attached only through $r$, because every alternative route would need a reticulate edge outside the tree cycle. Consequently the subtrees hanging from reticulations are atomic blocks for cluster containment: under any switching, the leaves below a tree edge are $L_e$ plus whole blocks $Y_r$, and a block is forced exactly when every incoming edge of $r$ starts below $w$. Existence follows from a construction attaching every leaf except one to a reticulation with two parents, one on each side of a split, which represents any cluster containing or avoiding the first taxon. For general rooted networks the cluster containment problem is NP-complete, so the galled condition is what buys tractability.

## Sources

- D. H. Huson, R. Rupp, V. Berry, P. Gambette, C. Paul, "Computing galled networks from real data", Bioinformatics (2009), Section 2 (hardwired and softwired representation, Definition 1, Lemma 1, Figures 1–2) and Section 3 (incompatibility graph and decomposition). <https://doi.org/10.1093/bioinformatics/btp217> (PMC2687971).
