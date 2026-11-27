# NP-hardness of the maximum parsimony distance on binary trees

For phylogenetic trees $\mathcal T_1,\mathcal T_2$ on the same taxon set $X$ and a character $f:X\to C$ (a finite set of states), let $l_f(\mathcal T)$ be the parsimony score of $f$ on $\mathcal T$ (the minimum number of edges whose endpoints receive different states over all extensions of $f$ to the internal vertices, computable by Fitch's algorithm). The **maximum parsimony (MP) distance** is

$$d_{MP}(\mathcal T_1,\mathcal T_2)=\max_f\bigl|l_f(\mathcal T_1)-l_f(\mathcal T_2)\bigr|,$$

the maximum over all characters on $X$; $d^{\,i}_{MP}$ denotes the same maximum restricted to characters with at most $i$ states. $d_{MP}$ is a metric on unrooted tree shapes and does not depend on rooting, since parsimony scores do not.

**Theorem.**

1. Computing $d_{MP}(\mathcal T_1,\mathcal T_2)$ is NP-hard even when both trees are binary.
2. For every fixed $i\ge4$, computing $d^{\,i}_{MP}$ on binary trees is NP-hard.
3. Computing the two-state distance $d^{\,2}_{MP}$ is NP-hard on binary trees, and in fact APX-hard: there is $\varepsilon>0$ such that no polynomial-time algorithm approximates $d^{\,2}_{MP}$ within a factor $1-\varepsilon$ unless $\mathrm P=\mathrm{NP}$.

Earlier hardness results needed multifurcating input trees; binary trees are the main case in practice. In the opposite direction the distance can be computed exactly for small instances by an integer linear program that assigns states to the vertices of both trees and maximizes the difference of the two (minimal) mutation counts.

## Depends on

- [Small parsimony problem](../../small-parsimony-problem/README.md)

## Expansion

Both reductions build, from a cubic graph $G=(V,E)$, a pair of binary trees $\mathcal T_E$ and $\mathcal T_V$ with leaves encoding edge–vertex incidences, together with a **symmetry-breaking gadget** (a large rigid subtree pattern) that forces every optimal character to satisfy $l_f(\mathcal T_V)<l_f(\mathcal T_E)$ and to have a prescribed structure, so that optimal characters correspond to colorings of $G$. For the unbounded-state case the reduction is from deciding whether the chromatic index of a cubic graph is $3$ (Holyer's NP-complete problem): for a computable integer $P$, $d_{MP}(\mathcal T_E,\mathcal T_V)=P$ if $G$ is $3$-edge-colorable and at most $P-1$ otherwise; optimal characters use a bounded number of states, which gives the fixed-$i$ corollary. For two states the reduction is from CUBIC MAX CUT, where a two-state character on $\mathcal T_V$ encodes a bipartition $V_1\cup V_2$ and the score difference counts cut edges up to an affine transformation; since CUBIC MAX CUT is APX-hard and the transformation preserves approximation ratios up to a constant, $d^{\,2}_{MP}$ is APX-hard. Several auxiliary gadget properties are verified computationally with the ILP.

## Sources

- Steven Kelk, Mareike Fischer, "On the complexity of computing MP distance between binary phylogenetic trees", arXiv (2014). Section 4 (symmetry-breaking construction and reduction from chromatic index; Theorem 4.6, Corollary 4.7), Section 5 (two-state reduction from CUBIC MAX CUT; Theorem 5.6, Corollary 5.7), Section 6 (ILP formulation). <https://doi.org/10.48550/arXiv.1412.4076>. Published version: Annals of Combinatorics 21(4) (2017), 573–604, <https://doi.org/10.1007/s00026-017-0361-1>; locators above refer to the arXiv version.
