# Tree-breaking invariance of unweighted UniFrac

**Setting.** Let $F = (V, E, R)$ be a rooted forest whose leaves $1, \dots, p$ carry abundance vectors $x \in \mathbb N^p$ for each sample, and for an edge $e$ let $\mathrm{ndesc}(e, x, F)$ be the number of individuals of sample $x$ descending from $e$ (the leaf abundance for a leaf edge, the sum over child edges otherwise). Unweighted UniFrac $d_u(x_1, x_2, F)$ is computed from the indicators $\mathbf 1(\mathrm{ndesc}(e, x, F) > 0)$ as in [UniFrac distances as branch sums](unifrac-distances-as-branch-sums.md). The *tree-breaking* operation $\mathrm{tb}(F, e)$ removes edge $e = (v_1, v_2)$ and attaches the lower endpoint to a new root vertex by a new edge of the same length, splitting one tree into two. Let $s(e, F)$ denote the sister branch of $e$.

**Theorem.**

1. If $s = s(e, F)$ has descendants in both samples, $\mathrm{ndesc}(s, x_1, F) > 0$ and $\mathrm{ndesc}(s, x_2, F) > 0$, then $d_u(x_1, x_2, F) = d_u(x_1, x_2, \mathrm{tb}(F, e))$.
2. For samples $x_1, \dots, x_n$, if the sister branch has descendants in every sample, breaking the tree at $e$ leaves all pairwise unweighted UniFrac distances $d_u(x_i, x_j)$ unchanged.

Thus unweighted UniFrac cannot distinguish a phylogeny from the forest obtained by cutting it above any clade whose sister clade is present in all samples; for microbiome data, where deep clades are nearly always present, it effectively ignores the deep structure of the tree.

## Depends on

- [UniFrac distances as branch sums](unifrac-distances-as-branch-sums.md)

## Expansion

Presence indicators propagate upward: if a branch has descendants in a sample, so do all its ancestors. When the sister of $e$ is present in a sample, every ancestor of $e$ is present in that sample regardless of $e$'s own subtree, so removing the link from $e$ to its parent changes no indicator on the remaining edges, and the new edge has the same indicator as the removed one. The weighted distances do change under tree-breaking, because descendant proportions on the ancestral edges change.

## Sources

- J. Fukuyama, "Emphasis on the deep or shallow parts of the tree provides a new characterization of phylogenetic distances", *Genome Biology* (2019), Appendix, Definitions 1–3, Lemma 1, Theorems 1–2 and Fig. 8. <https://doi.org/10.1186/s13059-019-1735-y> (PMC6599322)
