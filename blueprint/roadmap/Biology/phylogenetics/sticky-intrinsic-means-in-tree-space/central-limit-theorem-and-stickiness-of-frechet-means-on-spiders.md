# Central limit theorem and stickiness of Fréchet means on spiders

**Setting.** The space $T_3$ of phylogenetic trees with three leaves and one interior edge length is the **3-spider**: three half-lines (legs) glued at a common origin $C$, the star tree. More generally, a $p$-spider $S_p$ has legs $L_1,\dots,L_p$, each isometric to $[0,\infty)$, with the intrinsic (geodesic) metric. Distances between points on the same leg are differences, and distances between points on different legs pass through $C$. A probability measure $Q$ on $S_p$ decomposes as

$$Q(A) = w_0\,Q_0(A\cap C) + \sum_{k=1}^p w_k\,Q_k(A\cap L_k),$$

where $Q_k$ is a probability on $L_k$ with mean $\nu_k = \int u\,Q_k(du) > 0$. Let $X_1, X_2,\dots$ be i.i.d. with law $Q$ and finite second moment. Let $\mu_I$ be the intrinsic (Fréchet) mean, the minimizer of $x\mapsto\mathbb{E}\,d(x,X_1)^2$, and $\bar X_{n}$ the sample Fréchet mean. Both exist and are unique because $S_p$ is a CAT(0) space.

**Theorem.** Assume $w_0 = 0$ and write $v_k = w_k\nu_k$.

1. If $v_a > \sum_{b\ne a}v_b$ for some leg $a$, then $\mu_I \in L_a$ at distance $v_a - \sum_{b\ne a}v_b$ from $C$. For $n$ large, $\bar X_n\in L_a$ and $\sqrt n(\bar X_n - \mu_I)$ is asymptotically normal.
2. If $v_a = \sum_{b\ne a}v_b$ for some $a$, then $\mu_I = C$. After folding the other legs into one half-line opposite $L_a$, $\sqrt n\,\bar X_n$ is asymptotically distributed as the absolute value of a normal variable.
3. If $v_a < \sum_{b\ne a}v_b$ for every $a$, then $\mu_I = C$, and there is $n_0$ such that $\bar X_n = C$ almost surely for all $n\ge n_0$.

In case 3 the sample mean is **sticky**: it equals the star tree exactly for all large samples, so the usual $\sqrt n$ fluctuations vanish. Stickiness can be checked directly from leg weights and leg means, without fitting any model.

## Expansion

For $x$ at distance $x$ from $C$ on leg $L_a$, the Fréchet function is

$$F(x) = x^2 + 2\Big(\sum_{b\ne a}v_b - v_a\Big)x + \text{const},$$

because points on other legs are at distance $x+u$ and points on $L_a$ at distance $|x-u|$. On each leg $F$ is a quadratic with vertex at $v_a - \sum_{b\ne a}v_b$. If the vertex is positive on some leg, the minimum lies inside that leg. Otherwise every leg's quadratic increases away from $C$, so the minimizer is $C$. The sample version replaces $v_k$ by empirical leg averages. Under strict inequalities, the strong law of large numbers makes the sample signs agree with the population signs for all large $n$, which gives stickiness in case 3 and a Euclidean CLT in case 1. For four-leaf trees the space $T_4$ consists of $15$ quadrants glued along shared axes, and the source encodes such data through the associated Petersen graph. The source uses these results to compare samples of SARS-CoV-2 genome trees.

## Sources

- C. Shen, V. Patrangenaru and R. Moore, "A Phylogenetic Trees Analysis of SARS-CoV-2", arXiv:2106.06918 (2021), Section 3, Theorem 2 and Corollary 3, <https://doi.org/10.48550/arXiv.2106.06918>.
- T. Hotz et al., "Sticky central limit theorems on open books", Ann. Appl. Probab. (2013).
