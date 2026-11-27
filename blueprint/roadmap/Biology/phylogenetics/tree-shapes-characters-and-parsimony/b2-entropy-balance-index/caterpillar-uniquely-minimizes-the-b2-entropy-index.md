# The caterpillar uniquely minimizes the B2 entropy index

**Setting.** Let $T$ be a rooted tree (no vertex of out-degree $1$) with leaf set $V_L(T)$, $|V_L(T)|=n$. For a leaf $x$ let

$$p_x=\prod_{v\in anc(x)}\frac{1}{|child(v)|},$$

the probability of reaching $x$ by a random walk from the root that picks a child uniformly at each inner vertex (so $p_x=2^{-\delta_T(x)}$ in a binary tree, with $\delta_T(x)$ the depth of $x$). Shao and Sokal's **$B_2$ index** is the Shannon entropy of this distribution,

$$B_2(T)=-\sum_{x\in V_L(T)}p_x\log p_x ,$$

for an arbitrary but fixed logarithm base.

**Grafting identity.** If $T''$ is obtained by grafting a rooted tree $T'$ onto a leaf $x^\ast$ of $T$, then $B_2(T'')=B_2(T)+p_{x^\ast}B_2(T')$. In particular, for a binary tree with root split $T=(T_1,T_2)$, $B_2(T)=\tfrac12\bigl(B_2(T_1)+B_2(T_2)\bigr)+\log 2$ (equal to $+1$ in base $2$).

**Theorem.** For every $n\ge1$ and every logarithm base, the caterpillar $T^{cat}_n$ is the unique tree in $\mathcal{T}^\ast_n$ (arbitrary rooted trees, not only binary ones) with minimal $B_2$ index, and

$$\min_{T\in\mathcal T^\ast_n}B_2(T)=B_2(T^{cat}_n)=\log(2)\,\bigl(2-2^{-n+2}\bigr).$$

Moreover, every pending subtree of a $B_2$-minimal (respectively $B_2$-maximal) tree is itself $B_2$-minimal (maximal). On the other side, $B_2(T)\le\log n$ with equality iff $p_x=1/n$ for all leaves (e.g. the star tree), and among binary trees (base $2$) $B_2(T)\le\lfloor\log_2 n\rfloor+(n-2^{\lfloor\log_2 n\rfloor})/2^{\lfloor\log_2 n\rfloor}$, with equality exactly when all leaf depths differ by at most $1$. Hence $B_2$ is a balance index.

## Expansion

For a binary tree, $B_2(T)=\log 2\sum_x \delta_T(x)2^{-\delta_T(x)}$. The caterpillar has one leaf at each depth $1,\dots,n-2$ and two at depth $n-1$, so

$$B_2(T^{cat}_n)=\log 2\Bigl(\frac{n-1}{2^{n-1}}+\sum_{i=1}^{n-1}\frac{i}{2^i}\Bigr)=\log 2\,(2-2^{-n+2})$$

by induction on $n$. Binary minimality follows from the grafting identity: replacing any pending subtree by the caterpillar with the same number of leaves never increases $B_2$ and strictly decreases it unless the subtree already was one. For non-binary trees, take a smallest non-binary minimizer; all its pending subtrees are minimal, hence binary caterpillars, so only the root has $k>2$ children. If the root's children carry subtrees $T_1,\dots,T_k$, then for any two of them $p_x$ on $T_1\cup T_2$ is $\tfrac2k$ times its value in $(T_1,T_2)$, so $B_2$ of the whole tree equals $\tfrac2k B_2\bigl((T_1,T_2)\bigr)$ plus a term not depending on $(T_1,T_2)$; minimality forces every pair $(T_i,T_j)$ to be a caterpillar, so at most one $T_i$ has more than one leaf. An explicit regrafting of such a root-star-plus-caterpillar shape then lowers $B_2$, a contradiction. The value is independent of $n$ in the limit ($\to2\log2$), which is why the index separates imbalanced trees poorly but discriminates among balanced ones.

## Depends on

- [Balance and imbalance index axioms for rooted tree shapes](../axioms-of-tree-balance-indices/balance-and-imbalance-index-axioms.md)

## Sources

- Mareike Fischer, Lina Herbst, Sophie Kersting, Luise Kühn and Kristina Wicke, "Tree Balance Indices",  (2023), <https://doi.org/10.1007/978-3-031-39800-1>; numbering as in arXiv:2109.12281: $B_2$ index fact sheet and appendix: Proposition 17 (grafting identity), Theorems 5 and 6, Corollaries 6–7, Lemma 2.
- F. Bienvenu, G. Cardona, C. Scornavacca, "Revisiting Shao and Sokal's $B_2$ index of phylogenetic balance", Journal of Mathematical Biology (2021), Theorem 2.3 and Proposition 1.10.
