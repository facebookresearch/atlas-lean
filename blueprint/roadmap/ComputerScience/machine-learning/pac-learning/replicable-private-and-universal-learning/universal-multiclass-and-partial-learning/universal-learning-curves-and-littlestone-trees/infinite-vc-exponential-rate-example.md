# A class of infinite VC dimension learnable at exponential rate

Let $X = \bigsqcup_{k \ge 1} X_k$ be a disjoint union of finite sets with $|X_k| = k$, let $H_k = \{\mathbf{1}_S : S \subseteq X_k\}$ (functions on $X$ vanishing off $X_k$), and let $H = \bigcup_k H_k$. Then $\mathrm{VC}(H) = \infty$, so $H$ is not PAC learnable, but $H$ has no infinite Littlestone tree; consequently $H$ is learnable with optimal universal rate $e^{-n}$. Thus universal learnability at the fastest rate is not governed by the VC dimension.

## Proof sketch

Each $X_k$ is shattered by $H_k$, so the VC dimension is infinite. Fix the root point $x \in X_k$ of a Littlestone tree: only concepts of $H_k$ take the value $1$ at $x$, so the concepts consistent with the subtree for label $1$ form the finite class $H_k$, and a finite class has no infinite Littlestone tree; hence no infinite Littlestone tree exists. The exponential upper bound applies, and since $|H| \ge 3$ so does the exponential lower bound. ($X$ is countable, hence Polish with the discrete topology, and $H$ is countable, hence measurable.) PAC learnability fails by the fundamental theorem.

## Depends on

- [Infinite Littlestone trees](infinite-littlestone-tree.md)
- [Realizable distributions, learning curves and universal rates](universal-rate.md)

## Proof depends on

- [Classes with no infinite Littlestone tree are learnable at exponential rate](exponential-rate-upper-bound.md)
- [No class with three concepts is learnable faster than exponentially](exponential-rate-lower-bound.md)
- [The fundamental theorem of PAC learning](../../../is-paclearnable-realizable-family-iff-ha.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483, Example 2.3.
