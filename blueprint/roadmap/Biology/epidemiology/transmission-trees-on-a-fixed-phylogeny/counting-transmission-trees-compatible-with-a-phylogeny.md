# Counting transmission trees compatible with a phylogeny

Let $T$ be a rooted binary tree (a pathogen phylogeny without branch lengths) with node set $N(T)$ and $n$ tips, one tip per sampled host. A partition of $N(T)$ is **admissible** if each part contains exactly one tip and induces a connected subgraph of $T$. Under complete sampling, one sample per host and a complete bottleneck at transmission, admissible partitions are in bijection with transmission trees compatible with $T$ (the part of a host is the set of lineages present in that host). Let $\mathcal{P}(T)$ be the set of admissible partitions, and let $T^{*}$ be the tree obtained from $T$ by attaching one extra tip to its root by a new edge, viewed as an unrooted tree whose admissible partitions $\mathcal{P}(T^*)$ are defined in the same way. For an internal node $u$ write $T_u$ for the subtree rooted at $u$, and $r_L, r_R$ for the children of the root $r$.

**Proposition 1.** If $T$ has at least two tips,

$$|\mathcal{P}(T)| = |\mathcal{P}(T_{r_L})|\,|\mathcal{P}(T_{r_R}^{*})| + |\mathcal{P}(T_{r_R})|\,|\mathcal{P}(T_{r_L}^{*})| .$$

**Proposition 2.** If $T$ has at least two tips,

$$|\mathcal{P}(T^{*})| = |\mathcal{P}(T)| + |\mathcal{P}(T_{r_L}^{*})|\,|\mathcal{P}(T_{r_R}^{*})| .$$

With $|\mathcal{P}(T)| = |\mathcal{P}(T^*)| = 1$ for a single tip, both counts follow by one postorder traversal in $O(n)$ arithmetic operations.

**Proposition 3 (caterpillars).** If $\ell_n$ is the caterpillar (fully unbalanced) tree with $n$ tips, then $|\mathcal{P}(\ell_n)| = F_{2n-1}$ and $|\mathcal{P}(\ell_n^*)| = F_{2n}$, where $F_m$ is the $m$-th Fibonacci number ($F_1 = F_2 = 1$). For example $|\mathcal{P}(\ell_{10})| = 4181$.

## Expansion

$\mathcal{P}(T_u^*)$ counts the ways to partition $T_u$ when the root $u$ may also belong to a part coming from outside $T_u$ (the extra tip stands for "the host infecting the lineage above $u$"). In an admissible partition of $T$ the root $r$ belongs to the part of a tip in exactly one of the two subtrees: if it lies in the left subtree's tip set, the left subtree is partitioned admissibly on its own (with $r$ attached to the part containing $r_L$) while the right subtree's root may or may not join $r$'s part, contributing $|\mathcal{P}(T_{r_R}^*)|$; symmetrically for the right. This gives Proposition 1. For $T^*$ either $r$ joins the extra tip's part, in which case both subtrees are of the starred type, or it does not, which is counted by $|\mathcal{P}(T)|$. Proposition 3 follows by induction from Propositions 1–2 with the subtrees $\ell_{n-1}$ and $\ell_1$, using $F_{2n-3} + F_{2n-2} = F_{2n-1}$. Unbalanced phylogenies admit more transmission trees than balanced ones when infection times are unconstrained.

## Sources

- M. D. Hall, C. Colijn, "Transmission trees on a known pathogen phylogeny: enumeration and sampling", Molecular Biology and Evolution 36(6) (2019) 1333–1343, section "Enumeration of Possible Transmission Trees", Propositions 1–3, <https://doi.org/10.1093/molbev/msz058>, PMCID PMC6526902.
