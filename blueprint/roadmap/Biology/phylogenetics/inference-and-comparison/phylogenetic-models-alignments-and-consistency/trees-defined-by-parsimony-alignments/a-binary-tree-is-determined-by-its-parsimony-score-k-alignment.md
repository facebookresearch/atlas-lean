# A binary tree is determined by its parsimony-score-k alignment

**Setting.** For a binary phylogenetic $X$-tree $T$ with $n$ leaves and $k \ge 1$, let $A_k(T)$ be the set of binary characters on $X$ whose parsimony score on $T$ equals $k$, as defined in [the count of binary characters with parsimony score k](number-of-binary-characters-with-parsimony-score-k.md).

**Theorem.** Let $k \ge 1$ and $n \ge 20k$. For binary phylogenetic $X$-trees $T, \widetilde T$ with $|X| = n$,

$$T = \widetilde T \iff A_k(T) = A_k(\widetilde T).$$

**Context.** For $k = 1$ this is Buneman's theorem, since $A_1(T)$ is the set of splits $\Sigma(T)$ and binary trees are determined by their splits; for $k = 2$ it was known for all $n$. For every $k \ge 3$ the statement fails when $n = 2k$, so some lower bound on $n/k$ is necessary.

## Depends on

- [Number of binary characters with parsimony score k on a binary tree](number-of-binary-characters-with-parsimony-score-k.md)

## Proof sketch

If $T \ne \widetilde T$, Buneman's theorem gives a split $\sigma$ of $T$ that is not a split of $\widetilde T$, so its character has score $1$ on $T$ and at least $2$ on $\widetilde T$. The proof extends this character to one of score exactly $k$ on $T$ but a different score on $\widetilde T$: it recolors leaves inside a large side $B$ of the split (with $|B| \ge n/2$) to add $k - 1$ further changes, using the Menger characterization to certify the score through edge-disjoint leaf-to-leaf paths. One shows that $B$ contains at least $|B|/2 - 2\log_2|B| - 1.5$ edge-disjoint paths avoiding two chosen leaves, which exceeds $k - 2$ once $n \ge 20k$. The result says that, for trees with many leaves relative to $k$, the full set of maximum-parsimony-score-$k$ characters still pins down the tree, a prerequisite for consistency of parsimony on such alignments.

## Sources

- Mareike Fischer, "Defining Binary Phylogenetic Trees Using Parsimony", *Annals of Combinatorics* 27 (2023), 457–467, <https://doi.org/10.1007/s00026-022-00627-x>. Preprint version: arXiv:2111.04385 (2021), Theorem 2 (Buneman) and Corollary 1, Proposition 2 (Section 2.2), Theorem 3 and its proof (Section 3), <https://doi.org/10.48550/arXiv.2111.04385>.
