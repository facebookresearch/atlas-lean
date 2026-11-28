# Maximum parsimony recovers the generating tree within its NNI neighbourhood for few substitutions

**Setting.** Let $T$ be a binary phylogenetic $X$-tree with $|X| = n$. For a binary character $f : X \to \{a, b\}$, $l(f, T)$ is its parsimony score (minimum number of substitutions on $T$, computed by Fitch's algorithm), and for an alignment $A$, $l(A, T) = \sum_{f \in A} l(f, T)$. The $A_k$-alignment $A_k(T)$ consists of all binary characters $f$ with $l(f, T) = k$ (each character counted once, up to swapping $a$ and $b$). Two binary trees are NNI neighbours if one arises from the other by swapping two subtrees across an inner edge.

**Theorem.** Let $T, T'$ be NNI neighbours on $X$ with $|X| = n$, and let

$$0 < k < \frac{n}{8} + \frac{11}{9} - \frac{1}{18}\sqrt{9\Big(\frac{n}{4}\Big)^2 + 16}.$$

Then $l(A_k(T), T) < l(A_k(T), T')$: $T$ is the unique maximum parsimony tree for $A_k(T)$ within its NNI neighbourhood. The bound is asymptotically $k < n/12 + O(1)$. Consequently, if $n > 9k - 11 + \sqrt{9k^2 - 22k + 17}$, then any concatenation $A$ of copies of $A_0(T), \dots, A_k(T)$ satisfies $l(A, T) \le l(A, T')$, strictly if some $A_i(T)$ with $i > 0$ is included.

**Theorem (failure for large $k$).** For every $n \ge 8$ there is a binary tree $T$ on $n$ leaves with an NNI neighbour $T'$ such that $l(A_k(T), T) > l(A_k(T), T')$, for

$$k = \tfrac{n-4}{2},\ \tfrac{n-3}{2},\ \tfrac{n-2}{2},\ \tfrac{n-1}{2},\ \tfrac{n}{2} \quad \text{according as } n \bmod 8 \equiv 0;\ \{1,7\};\ \{2,6\};\ \{3,5\};\ 4.$$

So $T$ need not be a maximum parsimony tree of its own $A_k$-alignment once $k$ is of order $n/2$. (For $k = 1$, and for $k = 2$ when $n \ge 9$, $T$ is the unique maximum parsimony tree over all trees.)

## Proof sketch

An NNI move across the inner edge $e$ separating subtrees $T_1, T_2$ from $T_3, T_4$ changes a character's score only if the score on $e$ differs, by exactly one, between $T$ and $T'$, which forces conditions on the Fitch root-state sets of the four subtrees. Counting the characters with prescribed score and root-state set on a rooted tree, $N_{\{a\}}(T,k) = \binom{n-k-1}{k}2^k$ and $N_{\{a,b\}}(T,k) = \binom{n-k-1}{k-1}2^k$ (Steel), and comparing the characters that favour $T$ with those that favour $T'$ gives a quadratic inequality in $k$ whose root is the stated bound. Balanced choices of the four subtree sizes realise the reverse inequality near $k \approx n/2$.

## Sources

- Mareike Fischer, "On the Correctness of Maximum Parsimony for Data with Few Substitutions in the NNI Neighborhood of Phylogenetic Trees", *Annals of Combinatorics* 29 (2025), 615–635, <https://doi.org/10.1007/s00026-024-00725-y>. Preprint version: arXiv:2403.01282 (2024), Theorems 1–4, Proposition 1 and Corollary 2, <https://doi.org/10.48550/arXiv.2403.01282>.
