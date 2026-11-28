# Maximum parsimony trees need not have maximum parsimony subtrees

Let $X$ be a set of $m$ taxa and $S = f_1 \cdots f_n$ an alignment of characters $f_i : X \to \mathcal C$ (character states). For an unrooted binary phylogenetic $X$-tree $\mathcal T$, the parsimony score $l_{\mathcal T}(S) = \sum_i l_{\mathcal T}(f_i)$ counts the minimum number of state changes along the edges needed to explain the characters; a **maximum parsimony (MP) tree** minimizes it. For $Y \subseteq X$ write $\mathcal T|_Y$ and $S|_Y$ for the restrictions. A character is **homoplasy-free** on $\mathcal T$ if $l_{\mathcal T}(f) = |f(X)| - 1$.

**Heredity conjecture (PC5, Isaac Newton Institute 2007).** If $\mathcal T$ is an MP tree for $S$, then for each $k = 4, \dots, m-1$ there is a $k$-subset $Y \subseteq X$ such that $\mathcal T|_Y$ is an MP tree for $S|_Y$.

**Theorem.**

1. The conjecture holds if $S$ is homoplasy-free on $\mathcal T$ (deleting any taxon keeps every character homoplasy-free, so $\mathcal T|_Y$ is MP for every $Y$).
2. The conjecture holds for $m = 5$ taxa and binary characters: if $\mathcal T = ((1,2),3,(4,5))$ is an MP tree for a binary alignment, then $((1,2),(4,5))$ is an MP tree for the alignment with taxon $3$ deleted.
3. The conjecture fails for multistate characters on $5$ taxa, even when $\mathcal T$ is the unique MP tree.
4. The conjecture fails for binary characters on more than five taxa, even for a unique MP tree; in fact a unique MP tree may have no nontrivial MP subtree at all.
5. Compatibility of all MP quartet trees with a tree $\hat{\mathcal T}$ does not make $\hat{\mathcal T}$ an MP tree, even when all MP quartets and the MP tree are unique.

**Corollary (maximum likelihood).** Via the Tuffley–Steel equivalences (MP and maximum likelihood choose the same trees under the no-common-mechanism model, and ML trees are MP trees under the $N_r$ model for data with enough constant characters), the same failures hold for maximum likelihood: for $m \ge 5$ a unique ML tree may have no nontrivial ML subtree, and ML quartets compatible with a tree need not determine the ML tree.

So optimal phylogenies are not built up from optimal smaller phylogenies: adding or removing an outgroup can change the best topology of the remaining taxa, and quartet-based inductive or dynamic-programming arguments for MP and ML cannot rely on heredity.

## Proof depends on

- [No-common-mechanism maximum likelihood trees are maximum parsimony trees (Tuffley–Steel)](../../../../not-yet-classified/no-common-mechanism-parsimony/ncm-ml-iff-mp.md)

## Expansion

For homoplasy-free alignments the restricted tree attains the trivial lower bound $|f(Y)| - 1$ on every character, so it is optimal. The five-taxon binary case is an exhaustive comparison of the parsimony scores of the $15$ trees on five taxa against the $3$ quartets after deleting the middle taxon, using that binary characters split into a small number of patterns. The counterexamples come from writing the score of an alignment as $\sum_i x_i\,l_{\mathcal T}(f_i)$ over character patterns $f_i$ with multiplicities $x_i$: the requirements "$\mathcal T$ is the unique MP tree and no restriction is MP" become a system of linear inequalities in the $x_i$, solved by computer algebra and checked by exhaustive tree search (for six taxa, an explicit binary alignment whose unique MP tree $(((1,2),3),(4,(5,6)))$ has no MP five- or four-taxon subtree); the ML statements transfer the parsimony counterexamples through the Tuffley–Steel theorems.

## Sources

- Mareike Fischer, "Non-hereditary maximum parsimony trees", arXiv (2010). Section 2 (Conjecture PC5), Lemma 3.1, Theorems 3.2 and 3.3, Propositions 3.4–3.6, Theorems 3.7–3.8 (Tuffley–Steel), Corollaries 3.9 and 3.10. <https://doi.org/10.48550/arXiv.1007.3964>. Published version: Journal of Mathematical Biology 65(2) (2012), 293–308, <https://doi.org/10.1007/s00285-011-0458-9>; locators above refer to the arXiv version.
