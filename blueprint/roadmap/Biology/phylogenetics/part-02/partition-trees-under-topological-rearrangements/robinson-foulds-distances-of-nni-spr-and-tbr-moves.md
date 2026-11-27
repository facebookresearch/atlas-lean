# Robinson–Foulds distances of NNI, SPR and TBR moves

**Setting.** Let $T$ be an unrooted binary tree on a taxon set $X$, and $\Sigma(T)$ its set of splits (bipartitions of $X$ induced by interior edges). The [Robinson–Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md) $d_{RF}(T, T')$ between such trees on $X$ counts the splits in exactly one of $\Sigma(T)$ and $\Sigma(T')$, that is, $|\Sigma(T) \,\triangle\, \Sigma(T')|$.

**NNI.** Let $e$ be an interior edge whose four adjacent edges lead to subtrees with taxon sets $A,B,C,D$, with split $A \cup B \,|\, C \cup D$. A nearest-neighbour interchange swaps two subtrees across $e$, replacing that split by $A \cup D \,|\, B \cup C$ (or $A \cup C \,|\, B \cup D$); all other splits are unchanged, so the RF distance is $2$.

**SPR.** Let the subtree with taxa $A$ hang from the end of a path of interior edges $e_1,\dots,e_{n-1}$ from which subtrees with taxa $B_1,\dots,B_n$ hang in order, and let $T_{SPR}$ prune $A$ and regraft it onto the edge leading to $B_n$. Only the splits of the path edges change, one new split $B_1 \cup \dots \cup B_{n-1} \,|\, A \cup B_n$ appears and one disappears, and

$$d_{RF}(T, T_{SPR}) = 2(n-2).$$

For $n = 3$ this is an NNI.

**TBR.** Let $T_{TBR}$ be obtained by removing an interior edge $e$ and reconnecting the two components by a new edge joining the edge to $B_n$ on one side (path with subtrees $B_1,\dots,B_n$) and the edge to $C_m$ on the other (subtrees $C_1,\dots,C_m$), with $m \le n$ and $n > 2$. Then

$$d_{RF}(T, T_{TBR}) = 2(n+m-4).$$

For $m = 2$ the move is an SPR, and for $n = 3$, $m = 2$ an NNI.

## Depends on

- [Robinson–Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Expansion

In each move the splits of edges off the affected path are identical before and after, because the taxon sets on their two sides do not change. Along the SPR path, each of the $n-2$ interior path edges changes which side $A$ lies on, while the endpoint edges merge or split, giving $n-2$ distinct splits in each tree that are absent from the other. TBR combines two such paths, one per component, minus the shared edge $e$, which accounts for $2(n-2) + 2(m-2) = 2(n+m-4)$.

## Sources

- O. Chernomor, B. Q. Minh, A. von Haeseler, "Consequences of common topological rearrangements for partition trees in phylogenomic inference", Journal of Computational Biology 22(12) (2015) 1129–1142, Section 2, <https://doi.org/10.1089/cmb.2015.0146>, PMCID PMC4663649.
