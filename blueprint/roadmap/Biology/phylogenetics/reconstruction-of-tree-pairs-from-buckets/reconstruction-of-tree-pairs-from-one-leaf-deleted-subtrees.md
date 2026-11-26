# Reconstruction of a pair of phylogenetic trees from its $(n-1)$-bucket

**Setting.** A rooted phylogenetic tree on $n$ leaves is *labelled* when its leaves are bijectively labelled by a taxon set $X$ ($|X| = n$) and *unlabelled* otherwise. For $Y \subseteq X$ the subtree $T|_Y$ is the minimal connected subgraph containing the leaves in $Y$, with vertices of in- and out-degree $1$ suppressed (for unlabelled trees, take all $k$-leaf such subgraphs). The *$k$-multideck* $M_k(T)$ is the multiset of all $k$-leaf subtrees of $T$, and the *$k$-bucket* of a pair is the multiset union

$$B_k(\{T_1, T_2\}) = M_k(T_1) \uplus M_k(T_2).$$

The unordered pair $\{T_1, T_2\}$ is *recoverable from its $k$-bucket* if $B_k(\{T_1,T_2\}) = B_k(\{T_3,T_4\})$ implies $\{T_1,T_2\} = \{T_3,T_4\}$. The *root balance* of a rooted binary tree is the number of leaves of the smaller of the two subtrees hanging from the root.

**Theorem (monotonicity).** For $j \le k$, $B_j(\{T_1,T_2\})$ is determined by $B_k(\{T_1,T_2\})$.

**Theorem (unlabelled binary trees).** Let $T_1, T_2$ be unlabelled rooted binary phylogenetic trees on $n$ leaves.
1. If $n > 8$, $n < 4$ or $n = 5$, then $\{T_1, T_2\}$ is recoverable from its $(n-1)$-bucket.
2. If $n = 4$, no pair is recoverable from its $(n-1)$-bucket.
3. If $n \in \{6, 7, 8\}$, the pair is recoverable except for exactly two exceptional pairs for each $n$.
Moreover, for $n > 4$ the multiset of root balances $\{k_1, k_2\}$ is recoverable from the $(n-1)$-bucket.

**Theorem (labelled trees).** Let $T_1, T_2$ be labelled rooted phylogenetic trees on $X$ with $|X| = n$. If $n > 6$ or $n \le 4$, then $\{T_1, T_2\}$ is recoverable from its $(n-1)$-bucket; for $n \in \{5, 6\}$ it is recoverable except for a finite list of pathological pairs, up to relabelling. The key lemma: a labelled tree $T$ on $n$ leaves is the unique tree on $X$ having any four distinct given $(n-1)$-leaf subtrees of $T$ among its subtrees.

## Depends on

## Expansion

For a single tree, unlabelled binary trees on $n \ne 4$ leaves are determined by their $(n-1)$-multideck, and labelled trees by their $3$-multideck (rooted triples). For pairs, the bucket mixes two decks of size $n$ each. Deleting one leaf changes the root balance $r$ of an $n$-leaf tree to $r$ or $r - 1$ (or flips the major and minor subtree when they are nearly equal), so the root balances of the $2n$ cards determine $\{k_1, k_2\}$. Case analysis on $(k_1, k_2)$ then separates the cards of the two trees and rebuilds each tree from its own deck; small $n$ leave too few cards to separate and give the listed counterexamples. In the labelled case, the cards in which a given leaf is missing are identifiable from their leaf sets, and four distinct cards of one tree pin it down.

## Sources

- S. Basire and M. Hendriksen, "Tree Buckets and the Reconstruction of Pairs of Phylogenetic Trees", arXiv:2608.25446 (2026), Theorems 3.3, 3.17, 4.1, 4.11, 4.12, 6.1, 6.2 and 6.3, <https://doi.org/10.48550/arXiv.2608.25446>.
