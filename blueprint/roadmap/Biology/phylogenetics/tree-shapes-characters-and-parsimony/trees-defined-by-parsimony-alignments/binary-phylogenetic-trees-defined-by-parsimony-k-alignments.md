# Binary phylogenetic trees defined by their parsimony-k alignments

**Setting.** Let $T$ be a binary phylogenetic $X$-tree with $|X| = n$ leaves. A *binary character* is a map $f \colon X \to \{a, b\}$; an extension of $f$ labels all vertices of $T$, and the parsimony score $l(f, T)$ is the minimum number of edges whose endpoints get different labels. The *$A_k$-alignment* of $T$ is

$$A_k(T) = \{f \colon X \to \{a,b\} : l(f, T) = k\},$$

the set of all binary characters requiring exactly $k$ state changes on $T$. $A_k(T)$ *defines* $T$ if $A_k(T) = A_k(\widetilde T)$ forces $T \cong \widetilde T$ for every binary phylogenetic $X$-tree $\widetilde T$.

**Theorem.**
1. *(Global bound.)* For every $k \ge 1$ and $n \ge 4k$, $A_k(T)$ defines $T$: $T \cong \widetilde T$ if and only if $A_k(T) = A_k(\widetilde T)$. This lowers the previously known threshold $n \ge 20k$; for $k \in \{1, 2\}$ it holds for all $n$.
2. *(NNI neighborhood.)* For $k \ge 1$ and $n > 2k + 2$, if $\widetilde T$ is obtained from $T$ by one nearest neighbor interchange, then $A_k(T) = A_k(\widetilde T)$ only if $T \cong \widetilde T$.
3. *(Sharpness.)* For every $k > 2$ there are non-isomorphic binary phylogenetic $X$-trees $T, \widetilde T$ with $|X| \in \{2k+1, 2k+2\}$ and $A_k(T) = A_k(\widetilde T)$.

Hence the unknown range of $n$ shrinks from $[2k+1, 20k-1]$ to $[2k+3, 4k-1]$, and within NNI neighborhoods the threshold $n \ge 2k+3$ is exact; the authors conjecture that $n \ge 2k+3$ suffices globally for $k \ge 3$.

## Expansion

By Menger's theorem, $l(f, T)$ equals the maximum number of edge-disjoint (equivalently vertex-disjoint) paths in $T$ between the leaves labeled $a$ and those labeled $b$. When $n$ is large relative to $k$, one can route $k$ disjoint leaf-to-leaf paths that avoid any given split, so the characters of score $k$ detect every split of $T$ and hence the tree; a binary tree on $n$ leaves contains $\lfloor n/2 \rfloor$ edge-disjoint leaf-to-leaf paths with any prescribed leaf as an endpoint, which drives the $4k$ bound. For NNI neighbors a cherry-reduction induction compares the alignments directly. The result formalizes the folklore that maximum parsimony recovers the right tree from data with few substitutions per site.

## Sources

- Mirko Wilde and Mareike Fischer, "Defining binary phylogenetic trees using parsimony: New bounds", Discrete Applied Mathematics 341 (2023), 257–269, <https://doi.org/10.1016/j.dam.2023.08.005>; numbering as in arXiv:2303.03238: Section 2.1 (definitions), Corollary 1, Theorems 2–3, Lemma 2 and Corollary 3.
