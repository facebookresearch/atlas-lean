# When a rearrangement changes a partition tree

Use the trees, splits and moves of [Robinson–Foulds distances of NNI, SPR and TBR moves](robinson-foulds-distances-of-nni-spr-and-tbr-moves.md). For a partition with taxon set $Y \subseteq X$, the *partition tree* $T|_Y$ is the tree induced by $T$ on $Y$ (restrict to $Y$ and suppress degree-two vertices), with splits $\{\,P \cap Y \,|\, Q \cap Y : P|Q \in \Sigma(T)\,\}$.

**Proposition 1 (NNI).** Let $T_{NNI}$ be obtained from $T$ by an NNI around the interior edge $e$ with adjacent subtrees $A,B,C,D$. Then $T|_Y$ and $T_{NNI}|_Y$ have different topologies iff $Y$ meets each of $A,B,C,D$.

**Proposition 2 (SPR).** Let $T_{SPR}$ prune the subtree $A$ and regraft it onto the edge to $B_n$, along the path of subtrees $B_1,\dots,B_n$. For a partition with taxon set $Y$:

1. if $Y \cap A = \emptyset$, then $T|_Y = T_{SPR}|_Y$;
2. the topologies of $T|_Y$ and $T_{SPR}|_Y$ differ if $Y$ meets $A$ and at least three of $B_1,\dots,B_n$;
3. in that case the move induces an SPR on $T|_Y$ that prunes the subtree with split $A \cap Y \,|\, (B_1 \cup \dots \cup B_n) \cap Y$ and regrafts it onto the edge leading to $B_k \cap Y$, where $k$ is the largest index with $B_k \cap Y \ne \emptyset$.

**Proposition 3 (TBR).** Let $T_{TBR}$ cut the edge $e$ and reconnect the edges to $B_n$ and $C_m$. Then $T|_Y$ and $T_{TBR}|_Y$ differ if $Y$ meets at least one of $B_1,\dots,B_n$ and at least three of $C_1,\dots,C_m$, or at least one of the $C_j$ and at least three of the $B_i$. In that case the move induces a TBR on $T|_Y$ that cuts the edge with split $(B_1 \cup \dots \cup B_n) \cap Y \,|\, (C_1 \cup \dots \cup C_m) \cap Y$ and reconnects the edges leading to $B_k \cap Y$ and $C_h \cap Y$, where $k$ and $h$ are the largest indices with $B_k \cap Y \ne \emptyset$ and $C_h \cap Y \ne \emptyset$. If $Y$ misses all $B_i$ (or all $C_j$), the partition tree is unchanged.

## Depends on

- [Robinson–Foulds distances of NNI, SPR and TBR moves](robinson-foulds-distances-of-nni-spr-and-tbr-moves.md)

## Expansion

For an NNI swapping the subtrees below two edges, the only changed split $(A \cup B) \cap Y \,|\, (C \cup D) \cap Y$ becomes $(A \cup D) \cap Y \,|\, (B \cup C) \cap Y$; if one of the four intersections is empty both are trivial or already shared, so the induced quartet is missing and the RF distance of the partition trees is $0$. For SPR, every split in the symmetric difference separates $A$ from some of the $B_i$, so all coincide after restriction when $Y$ misses $A$; a visible change needs an induced quartet, i.e. $A$ and three of the $B_i$. In tree search with many partially sampled partitions, these conditions identify partitions whose likelihood need not be recomputed after a move, which is the speed-up the source exploits.

## Sources

- O. Chernomor, B. Q. Minh, A. von Haeseler, "Consequences of common topological rearrangements for partition trees in phylogenomic inference", Journal of Computational Biology 22(12) (2015) 1129–1142, Propositions 1–3, <https://doi.org/10.1089/cmb.2015.0146>, PMCID PMC4663649.
