# NP-completeness of the Robinson–Foulds distance between mul-trees

**Definitions.** A *mul-tree* $\mathcal T = (T, \varphi)$ on a label set $X$ is an unrooted tree $T$ with a surjective leaf labeling $\varphi : \mathcal L(T) \to X$; several leaves may carry the same label (gene copies of one species). A *full differentiation* of $\mathcal T$ is a singly labeled tree $(T, \varphi')$ with the same underlying tree and a bijective labeling, obtained by giving distinct new labels to leaves sharing a label. Two mul-trees $\mathcal T$ and $\mathcal S$ on the same label set $X$ have *matching label multiplicities* if every label occurs equally often in both; full differentiations $(T, \varphi')$ and $(S, \phi')$ are *consistent* if for each $a \in X$ the copies of $a$ receive the same set of new labels in both trees, so that $T'$ and $S'$ have the same leaf set. For mul-trees with matching label multiplicities,

$$\mathrm{RF}(\mathcal T, \mathcal S) = \min\{\mathrm{RF}(T', S') : T', S' \text{ consistent full differentiations of } \mathcal T, \mathcal S\},$$

where on the right RF is the ordinary [Robinson–Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md) on that common leaf set, the number of splits present in exactly one of the two singly labeled trees (for unrooted binary trees, the linked definition).

**Theorem.** Deciding whether $\mathrm{RF}(\mathcal T, \mathcal S) \le d$ for two mul-trees $\mathcal T, \mathcal S$ and an integer $d$ is NP-complete.

## Depends on

- [Robinson–Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Expansion

Membership in NP is immediate: a consistent full differentiation is a polynomial certificate whose RF distance is computed in linear time. Hardness comes from the freedom to match copies: for a label with $c$ copies there are $c!$ ways to pair the copies of the two trees, and the reduction encodes a combinatorial choice in these pairings. The hardness is specific to comparing two genuinely multi-labeled trees; when one tree is the extension of a singly labeled species tree the choice no longer matters.

## Sources

- R. Chaudhary, J. G. Burleigh and D. Fernández-Baca, "Inferring species trees from incongruent multi-copy gene trees using the Robinson-Foulds distance", *Algorithms for Molecular Biology* 8 (2013) 28, Section "Mul-trees and RF distance", Theorem 1 (proof in Additional file 1) and Theorem 2 (from the cited prior work). <https://doi.org/10.1186/1748-7188-8-28> (PMC3874668)
