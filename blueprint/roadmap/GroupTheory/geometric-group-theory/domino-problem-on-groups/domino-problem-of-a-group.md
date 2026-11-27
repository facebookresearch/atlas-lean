# Domino problem of a finitely generated group

The domino problem of a finitely generated group $G$ asks for an algorithm that decides, given a finite alphabet and a finite set of forbidden patterns, whether some coloring of $G$ by the alphabet avoids every translate of every forbidden pattern.

Let $G$ be a group with a finite generating set $S$ and let $\mathcal{A}$ be a finite alphabet. A configuration is a map $x\colon G \to \mathcal{A}$, and $G$ acts on the set $\mathcal{A}^G$ of configurations by translation, $(g \cdot x)(h) = x(g^{-1}h)$. A pattern is a map $p\colon F \to \mathcal{A}$ defined on a finite set $F \subseteq G$, its support; it appears in $x$ if some translate $g \cdot x$ agrees with $p$ on $F$. For a set $\mathcal{F}$ of patterns, the subshift

$$
X_{\mathcal{F}} = \{ x \in \mathcal{A}^G : \text{no pattern of } \mathcal{F} \text{ appears in } x \}
$$

is of finite type when $\mathcal{F}$ is finite. Patterns are coded by writing each element of their support as a word over $S \cup S^{-1}$. The domino problem of $G$ is the set of codings of finite sets of patterns $\mathcal{F}$ (over some finite alphabet) with $X_{\mathcal{F}} \ne \emptyset$; $G$ has decidable domino problem if this set is recursive, and undecidable domino problem otherwise.

## Depends on

- [Group](../../group-basics/group.md)

## Proof depends on

None.

## Expansion

For two finite generating sets the two domino problems are many-one equivalent, so decidability is a property of the group; it is also invariant under commensurability, and a group containing a finitely generated subgroup with undecidable domino problem has undecidable domino problem. The complement of the domino problem, the set of finite sets $\mathcal{F}$ with $X_{\mathcal{F}} = \emptyset$, is recursively enumerable when $G$ is finitely presented or has decidable word problem, by compactness. For $G = \mathbb{Z}^2$ with nearest-neighbour patterns this is the Wang tiling problem. Some sources define the domino problem as the set of $\mathcal{F}$ with $X_{\mathcal{F}} = \emptyset$; this is the complement and has the same decidability.

## Sources

- N. Aubrun, S. Barbieri and E. Moutot, "The domino problem is undecidable on surface groups", 44th International Symposium on Mathematical Foundations of Computer Science (MFCS 2019), Leibniz International Proceedings in Informatics (LIPIcs) 138 (2019), article 46, https://doi.org/10.4230/LIPIcs.MFCS.2019.46; arXiv:1811.08420v1 (Section 2.1, definition of subshifts and of the domino problem on graphs and finitely generated groups, in arXiv:1811.08420v1).
- N. Aubrun, S. Barbieri and M. Sablik, "A notion of effectiveness for subshifts on finitely generated groups", Theoretical Computer Science 661 (2017), 35–55, https://doi.org/10.1016/j.tcs.2016.11.033; arXiv:1412.2582v3 (Section 3 of arXiv:1412.2582v3, subsection "Application: A class of groups with undecidable domino problem", where the domino problem is the set of codings of finite pattern sets with empty subshift).
