# Trees with identical A_k-alignments are linked by k-problematic NNI moves

**Setting.** Let $T, \widetilde T$ be binary phylogenetic $X$-trees and $k \ge 2$, with $A_k(T)$ the set of binary characters of parsimony score exactly $k$ on $T$. Call a nearest-neighbour interchange from $T$ to $\widetilde T$ across an inner edge with pending subtrees of sizes $n_1,\ldots,n_4$ a *$k$-problematic move* if

$$s(T,\widetilde T) = \sum_{i=1}^4 \Big\lfloor \frac{n_i-1}{2}\Big\rfloor < k-2,$$

which is exactly the condition under which an NNI preserves the $A_k$-alignment.

**Theorem.** $A_k(T) = A_k(\widetilde T)$ if and only if $\widetilde T$ can be obtained from $T$ (up to isomorphism) by a finite series of $k$-problematic moves.

**Corollaries.**

- If $n \ge 2k+1$ and $A_k(T) = A_k(\widetilde T)$, then $T$ and $\widetilde T$ have exactly the same cherries.
- Problematic moves exist only when $n \le 2k+2$, so for $n \ge 2k+3$ the $A_k$-alignment determines the tree; for $n < 2k$ all trees share the empty alignment.

## Depends on

- [A_k-alignments determine binary phylogenetic trees with at least 2k+3 leaves](ak-alignments-determine-binary-trees-with-at-least-2k-plus-3-leaves.md)

## Expansion

Sufficiency is immediate from the NNI criterion applied move by move. For necessity, the remaining cases are $n \in \{2k, 2k+1, 2k+2\}$. The proof uses that equal alignments force equal cherries when $n \ge 2k+1$, and then reduces a shared cherry in two ways: deleting one leaf of the cherry, or deleting both and relabelling, which turns the question into one about $A_k$ and $A_{k-1}$ on smaller trees. Induction on $n$ and $k$ then assembles a chain of problematic moves.

## Sources

- Mirko Wilde and Mareike Fischer, "A Complete Characterization of Pairs of Binary Phylogenetic Trees with Identical $A_k$-Alignments", Annals of Combinatorics (2026), <https://doi.org/10.1007/s00026-026-00848-4>; numbering as in arXiv:2408.07011: Corollary 1 (cherry reduction), Proposition 4 and Theorem 6.
