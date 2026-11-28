# Number of binary characters with parsimony score k on a binary tree

**Setting.** Let $T$ be a binary phylogenetic $X$-tree with $|X| = n$ leaves. A binary character is a map $f: X \to \{a, b\}$, normalized by $f(1) = a$ so that $f$ and its state-swapped copy are identified (binary characters then correspond to $X$-splits). An extension $g$ of $f$ assigns states to all vertices of $T$ and agrees with $f$ on $X$; its changing number $ch(g)$ is the number of edges whose endpoints get different states. The parsimony score is $l(f, T) = \min_g ch(g)$. Let $A_k(T)$ be the set of binary characters with $l(f, T) = k$, the *alignment induced by $T$ and $k$*.

**Theorem (Steel).** For $k \ge 1$ with $2k \le n$,

$$|A_k(T)| = \frac{2n - 3k}{k}\binom{n - k - 1}{k - 1}\,2^{k-1}.$$

In particular $|A_k(T)|$ depends only on $n$ and $k$, not on the shape of $T$; for $k = 1$ it equals $2n - 3$, the number of edges (splits) of $T$.

**Menger characterization.** For binary $f$, $l(f, T)$ equals the maximum number of edge-disjoint leaf-to-leaf paths in $T$, each joining a leaf in state $a$ to a leaf in state $b$.

## Proof sketch

A character with score $k$ corresponds to a set of $k$ edges of $T$ whose removal leaves components that are monochromatic, with the two states differing across each removed edge; Steel counts these edge configurations on a binary tree and obtains a formula depending only on $n$ and $k$. As a check, for $n = 6$ the formula gives $9$, $18$ and $4$ characters of scores $1, 2, 3$, which together with the constant character account for all $2^5 = 32$ normalized binary characters. The Menger statement is max-flow/min-cut on the tree with the two leaf classes as source and sink. Since $|A_k(T)|$ is shape-independent, whether $A_k(T)$ determines $T$ is a purely structural question, settled by the theorem that $A_k(T)$ determines $T$ once $n \ge 20k$.

## Sources

- Mareike Fischer, "Defining Binary Phylogenetic Trees Using Parsimony", *Annals of Combinatorics* 27 (2023), 457–467, <https://doi.org/10.1007/s00026-022-00627-x>. Preprint version: arXiv:2111.04385 (2021), Section 2.1 (definitions) and Section 2.2 (Theorem 1, quoting M. Steel, *Phylogeny: Discrete and Random Processes in Evolution*, SIAM 2016; Proposition 1, adapted from Semple and Steel, *Phylogenetics*, Corollary 5.1.8), <https://doi.org/10.48550/arXiv.2111.04385>.
