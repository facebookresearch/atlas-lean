# A_k-alignments determine binary phylogenetic trees with at least 2k+3 leaves

**Definitions.** Let $X$ be a finite taxon set with $|X| = n$ and $T$ an unrooted binary phylogenetic $X$-tree. For a binary character $f: X \to \{a,b\}$ let $l(f,T)$ be its Fitch parsimony score on $T$. The *$A_k$-alignment* of $T$ is

$$A_k(T) = \{ f : X \to \{a,b\} \ :\ l(f,T) = k \}.$$

For $k=1$ the characters in $A_1(T)$ induce exactly the splits $\Sigma(T)$ of $T$. By Menger's theorem, $l(f,T)$ equals the maximum number of edge-disjoint paths in $T$ joining $f^{-1}(a)$ to $f^{-1}(b)$, and

$$|A_k(T)| = \frac{2n-3k}{k}\binom{n-k-1}{k-1}\, 2^k ,$$

independent of the shape of $T$. In particular $A_k(T) = \emptyset$ whenever $n < 2k$.

**Theorem.** Let $k \ge 1$ and let $T, \widetilde T$ be binary phylogenetic $X$-trees with $n \ge 2k+3$. Then $T \cong \widetilde T$ if and only if $A_k(T) = A_k(\widetilde T)$.

**NNI criterion.** Let $T$ have an inner edge $A|B$ separating pending subtrees with leaf sets $A_1, A_2$ (on the $A$ side) and $B_1, B_2$ (on the $B$ side), of sizes $n_1,\ldots,n_4$, and let $\widetilde T$ be obtained by exchanging the subtrees on $A_2$ and $B_2$ (a nearest-neighbour interchange). With $s(T,\widetilde T) = \sum_{i=1}^4 \lfloor (n_i-1)/2\rfloor$,

$$A_k(T) = A_k(\widetilde T) \iff s(T,\widetilde T) < k-2 .$$

## Expansion

Since $|A_k(T)|$ does not depend on $T$, the sizes alone never distinguish trees; the question is purely about which characters occur. The NNI criterion counts how many edge-disjoint leaf-to-leaf paths can be packed inside the four pending subtrees: if fewer than $k-2$ fit there, every score-$k$ character must use the central edge structure in the same way on both trees, so the alignments coincide. When $n \ge 2k+3$ the inequality fails for every NNI neighbour, and a cherry-reduction induction (a shared cherry reduces the question to $A_k$ and $A_{k-1}$ on smaller trees) extends the uniqueness from NNI neighbours to all pairs. The bound $2k+3$ is sharp: for $n = 2k+2$ there are distinct trees with equal $A_k$-alignments.

## Sources

- Mirko Wilde and Mareike Fischer, "A Complete Characterization of Pairs of Binary Phylogenetic Trees with Identical $A_k$-Alignments", Annals of Combinatorics (2026), <https://doi.org/10.1007/s00026-026-00848-4>; numbering as in arXiv:2408.07011: Theorem 3 (alignment size), Proposition 3 (NNI criterion) and Theorem 5.
