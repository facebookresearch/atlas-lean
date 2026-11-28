# GFB trees minimize concave subtree-size indices

**Setting.** Let $\mathcal{BT}^*_n$ be the set of rooted binary tree shapes with $n$ leaves. For an internal vertex $v$ of $T$ let $n_v$ be the number of leaves below $v$, and let $\mathring V(T)$ be the set of internal vertices. The *GFB tree* $T_n^{gfb}$ starts from a forest of $n$ single vertices and repeatedly joins two of the smallest remaining trees until one tree is left. The *caterpillar* $T_n^{cat}$ has exactly one cherry. For $f:\mathbb R_{\ge2}\to\mathbb R$ define

$$\Phi_f(T)=\sum_{v\in\mathring V(T)} f(n_v),\qquad \pi_c(T)=\prod_{v\in\mathring V(T)}(n_v+c).$$

**Theorem (minimum, Section 4.1).** For $n\ge2$ and $f$ strictly increasing and strictly concave, $T_n^{gfb}$ is the unique tree in $\mathcal{BT}^*_n$ minimizing $\Phi_f$.

**Theorem (maximum, Section 4.2).** For $n\ge2$ and $f$ strictly increasing, $T_n^{cat}$ is the unique tree maximizing $\Phi_f$.

**Corollary (product functions).** For $c>-2$ and any strictly increasing $g$, $T_n^{gfb}$ is the unique minimizer of $g(\pi_c(T))$. In particular the $\widehat s$-shape statistic $\sum_v\log(n_v-1)$ ($c=-1$, $g=\log$) and Fill's $Q$-shape statistic ($c=0$) are uniquely minimized by the GFB tree and maximized by the caterpillar, so both are imbalance indices.

**Distinctness (Section 4.2).** For distinct $c_1,c_2>-2$ there are trees $T,T'$ ranked oppositely by $\pi_{c_1}$ and $\pi_{c_2}$, so the family $\{\pi_c\}$ contains infinitely many genuinely different imbalance indices, and each $g(\pi_c)$ induces the same ranking as some $\Phi_{f_c}$ with $f_c$ strictly increasing and strictly concave.

## Expansion

Minimality is proved by a smallest-counterexample argument. GFB trees are closed under taking maximal pending subtrees, so if a minimizer $T$ were not GFB, replaying the greedy clustering inside $T$ produces two pending subtrees $T_a,T_b$ that are siblings in $T_n^{gfb}$ but not in $T$. In each of the two possible configurations, regrafting so that $T_a$ and $T_b$ become siblings changes the sizes of a chain of ancestors; strict concavity makes the sum of $f$ over the new sizes strictly smaller, contradicting minimality. The product case follows by taking logarithms, since $\log(n_v+c)$ is strictly increasing and strictly concave on $n_v\ge2$ when $c>-2$. The maximum uses only monotonicity: the caterpillar realizes the largest possible multiset of subtree sizes $\{2,3,\dots,n\}$.

## Depends on

- [Clade size metaconcept and its extremal trees](../tree-balance-metaconcepts/clade-size-metaconcept.md)

## Sources

- S. Cleary, M. Fischer, K. St. John, "The GFB Tree and Tree Imbalance Indices", *Bulletin of Mathematical Biology* 87(10) (2025), 145, Section 4.1 (minimization theorem and product-function corollary) and Section 4.2 (caterpillar maximization and distinctness propositions), <https://doi.org/10.1007/s11538-025-01522-1> (preprint arXiv:2502.12854).
