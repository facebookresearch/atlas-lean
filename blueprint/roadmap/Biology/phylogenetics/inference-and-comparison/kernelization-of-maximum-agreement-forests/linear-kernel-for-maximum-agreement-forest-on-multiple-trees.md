# Linear kernel for maximum agreement forest on multiple trees

**Setting.** Let $\mathcal T$ be a set of $t\ge 2$ binary phylogenetic trees on a common taxon set $X$, all unrooted or all rooted. An *agreement forest* of $\mathcal T$ is a partition of $X$ into blocks such that, in every tree, the minimal subtrees spanned by different blocks are vertex-disjoint and each block induces the same (suppressed) topology in all trees; the *maximum agreement forest* problem asks for the minimum number $k$ of blocks. For $m\ge1$ a sequence $C=(x_1,\dots,x_m)$ of distinct taxa is an *$m$-chain* of a tree if for each $i<m$ the parent of $x_i$ equals or is adjacent to the parent of $x_{i+1}$, and a *common chain* if it is a chain in every tree of $\mathcal T$. Two reduction rules are used:

- *subtree reduction:* a pendant subtree common to all trees is replaced by a single taxon;
- *chain reduction:* a common $m$-chain with $m>r$ is truncated to $r$ of its taxa in every tree, where

$$r=\min\{\max\{k,3\},\ t+1\} .$$

**Statement.**

1. Both rules are safe: after applying either rule, $\mathcal T$ has an agreement forest with at most $k$ blocks if and only if the reduced instance does.
2. (Unrooted kernel) If $\mathcal T$ consists of $t$ unrooted binary trees, has an unrooted agreement forest of size at most $k$, and neither rule applies, then every tree has at most $4trk-4tr-3rk$ taxa.
3. (Rooted kernel) If $\mathcal T$ consists of $t$ rooted binary trees, has a rooted agreement forest of size at most $k_r$, and neither rule applies, then every tree has at most $(2tr+1)(k_r-1)-r$ taxa, with $r=\min\{\max\{k_r,3\},t+1\}$.

Hence the problem has a kernel with $O(t\cdot r\cdot k)$ taxa. The truncation length $r$ cannot in general be decreased: there are instances with $t\ge3$ trees for which truncating common chains to $t$ instead of $t+1$ taxa changes the optimum, and instances showing that $k$ cannot be replaced by $k-1$. For $t=2$ (so $r=3$) the unrooted bound is $15k-24=15d_{\mathrm{TBR}}-9$ with $d_{\mathrm{TBR}}=k-1$, matching the known tight kernel under subtree and chain reduction, and the rooted bound likewise matches the known kernel in terms of $d_{\mathrm{rSPR}}=k_r-1$.

## Expansion

Fix an agreement forest $F$ of size $k$. For each tree $T$ and block $B$, let $\deg^T(B)$ be the number of edges of $T$ leaving the subtree spanned by $B$; contracting blocks shows $\sum_B \deg^T(B)\le 2k-2$. In a fully reduced instance a block cannot contain long stretches of taxa that hang off the same path in every tree, since these would form a common pendant subtree or a common chain longer than $r$; this gives $|B|\le 2r\sum_{T}\deg^T(B)-3r$. Summing over the $k$ blocks and using the degree bound gives $|X|\le 2r\,t(2k-2)-3rk$. Safety of chain truncation is the delicate part: one shows that an agreement forest of the truncated instance with at most $k$ blocks can be extended to the full chain without increasing the number of blocks, provided at least $\min\{\max\{k,3\},t+1\}$ chain taxa are kept; the tightness examples show that both arguments of the minimum are needed.

## Sources

- Steven Kelk, Ruben Meuwese, Leo van Iersel, "A kernel for the maximum agreement forest problem on multiple binary phylogenetic trees", *Journal of Graph Algorithms and Applications* 30(1) (2026), 363–383, Lemma 1, Lemma 2, Lemma 3, Lemma 4, Theorem 1 and Theorem 2, <https://doi.org/10.7155/jgaa.v30i1.3194> (preprint arXiv:2602.22281).
