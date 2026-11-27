# A class of infinite VC dimension learnable at exponential rate

Let $X = \bigsqcup_{d \ge 1} X_d$ be a disjoint union of finite blocks with $|X_d| = d$, and let $H$ consist of all functions $h : X \to \{0,1\}$ whose support is contained in a single block. Then $\mathrm{VC}(H) = \infty$, but $H$ has no infinite Littlestone tree; consequently $H$ has optimal universal rate $e^{-n}$, while it is not PAC learnable. Thus universal learnability at the fastest rate is not governed by the VC dimension.

## Proof sketch

Each block $X_d$ is shattered, so the VC dimension is infinite. In a Littlestone tree, consider the branch that takes label $1$ at the root point $x \in X_d$: all later nodes on that branch must also admit label $1$ in both subtrees, which forces their points into $X_d$, and a point already on the path cannot carry both labels, so the branch has depth at most $d+1$. Hence no infinite Littlestone tree exists, and the exponential-rate theorem applies; PAC learnability fails by the fundamental theorem.

## Depends on

- [Infinite Littlestone trees](infinite-littlestone-tree.md)
- [Realizable distributions, learning curves and universal rates](universal-rate.md)

## Proof depends on

- [Classes with no infinite Littlestone tree are learnable at exponential rate](exponential-rate-upper-bound.md)
- [The fundamental theorem of PAC learning](../../../is-paclearnable-realizable-family-iff-ha.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483.
