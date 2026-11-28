# The maximum parsimony distance is a metric bounded by the SPR distance

Let $T_1, T_2$ be phylogenetic trees (rooted or unrooted) on a taxon set $X$ with $|X| = n$. A character is a map $f : X \to \{1,\dots,r\}$ and $l_f(T)$ its parsimony score on $T$ (the minimum number of edges whose endpoints receive different states, over extensions of $f$ to all vertices). The **maximum parsimony distance** is

$$

d_{MP}(T_1,T_2) = \max_f\,\big|l_f(T_1) - l_f(T_2)\big|,

$$

the maximum over all characters on $X$ with any number of states. A character with $r$ states is **convex** on $T$ if $l_f(T) = r - 1$.

**Theorem.**

1. $d_{MP}$ is a metric on phylogenetic $X$-trees: it is nonnegative, zero exactly when $T_1 = T_2$, symmetric, and satisfies the triangle inequality.
2. (Convex characters suffice.) For any character $f$ that is convex on neither tree and satisfies $l_f(T_1) \ge l_f(T_2)$ there is a character $\hat f$, with at least as many states, that is convex on $T_2$ and has $|l_{\hat f}(T_1) - l_{\hat f}(T_2)| \ge |l_f(T_1) - l_f(T_2)|$; symmetrically, if $l_f(T_1) \le l_f(T_2)$, such an $\hat f$ exists that is convex on $T_1$. (Convexity on the tree with the smaller score is essential: for the caterpillar $T_1 = ((1,2),3,4,(5,6))$, the star $T_2$ on $6$ leaves and $f = AABBAB$, $l_f(T_1) = 2 < 3 = l_f(T_2)$, while every character convex on the star has difference $0$.) This corrects the first sentence of Theorem 3.6 of arXiv:1402.1553, which says that $\hat f$ can always be taken convex on $T_2$; its proof assumes $l_f(T_1) \ge l_f(T_2)$, and the example shows that the unconditional statement fails. Hence $d_{MP}$ is attained by a character convex on one of the two trees. If the number of states is fixed, this can fail, and for every $r > 1$ there are binary trees on $(r+1)^2$ taxa for which every $r$-state character does strictly worse than some $(r+1)$-state character.
3. (SPR lower bound.) For binary trees, $|l_f(T_1) - l_f(T_2)| \le d_{SPR}(T_1,T_2)$ for every character $f$, so $d_{MP}(T_1,T_2) \le d_{SPR}(T_1,T_2)$. For rooted binary trees with unrooted versions $\tilde T_i$, $d_{MP}(T_1,T_2) = d_{MP}(\tilde T_1,\tilde T_2) \le d_{SPR}(\tilde T_1,\tilde T_2) \le d_{rSPR}(T_1,T_2)$.
4. (Diameter bound.) $d_{MP}(T_1,T_2) \le n - 2\sqrt n + 1$.

## Expansion

The triangle inequality follows from $|l_f(T_1) - l_f(T_3)| \le |l_f(T_1) - l_f(T_2)| + |l_f(T_2) - l_f(T_3)|$ for each fixed $f$, and $d_{MP} > 0$ for distinct trees because a two-state character given by a split of one tree that is absent from the other scores $1$ on the first and at least $2$ on the second. The SPR bound uses the theorem of Bruen and Bryant that exactly $l_f(T) - (r-1)$ SPR moves are needed to make an $r$-state character $f$ convex: one SPR move changes any parsimony score by at most one. For item 2, states are split along the edges of $T_2$ until the character becomes convex there, and each split increases the score on $T_1$ at least as much as on $T_2$. The diameter bound is tight: there are pairs of trees on $9$ taxa attaining $n - 2\sqrt n + 1 = 4$.

## Sources

- Mareike Fischer, Steven Kelk, "On the Maximum Parsimony distance between phylogenetic trees", arXiv (2014); Annals of Combinatorics (2016). Section 3 (Definition 3.1, Theorems 3.2, 3.6, 3.8, 3.11, 3.15–3.16, Corollary 3.12). <https://doi.org/10.48550/arXiv.1402.1553>. Published version: Annals of Combinatorics 20(1) (2016), 87–113, <https://doi.org/10.1007/s00026-015-0298-1>; locators above refer to the arXiv version.
