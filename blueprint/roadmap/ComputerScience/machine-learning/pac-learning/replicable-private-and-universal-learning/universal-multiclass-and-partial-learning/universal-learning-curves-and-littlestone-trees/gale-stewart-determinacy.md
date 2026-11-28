# The learning game is determined, and the adversary wins exactly on an infinite Littlestone tree

Let $H \subseteq \{0,1\}^X$ and let $\mathfrak{G}$ be the learning Gale–Stewart game of $H$. Then:

1. exactly one of the two players has a winning strategy in $\mathfrak{G}$;
2. the adversary $P_A$ has a winning strategy if and only if $H$ has an infinite Littlestone tree, so the learner $P_L$ has one if and only if $H$ has no infinite Littlestone tree;
3. if $X$ is a Polish space and $H$ is measurable (there are a Polish space $\Theta$ and a Borel map $h : \Theta \times X \to \{0,1\}$ with $H = \{h(\theta, \cdot) : \theta \in \Theta\}$), then the winning player has a universally measurable winning strategy; in particular, when $H$ has no infinite Littlestone tree, $P_L$ has one.

## Proof sketch

Item 1 is the Gale–Stewart theorem for open games, since the winning set of $P_L$ is finitely decidable (the two move sets $X$ and $\{0,1\}$ can be merged into one move set, with an illegal move losing). For item 2, an infinite Littlestone tree $\{x_{\mathbf{u}}\}$ gives the strategy $\xi_\tau = x_{\eta_1 \cdots \eta_{\tau-1}}$ for $P_A$, which keeps every $H_{\xi_1, \eta_1, \dots, \xi_\tau, \eta_\tau}$ nonempty; conversely, the moves of a winning strategy of $P_A$, indexed by the replies of $P_L$, form an infinite Littlestone tree. Item 3 uses game values (ordinal ranks of positions): under the measurability assumption the set of positions from which $P_L$ wins is coanalytic, the values are countable ordinals by the Kunen–Martin theorem, and choosing moves that decrease the value gives a universally measurable strategy.

## Depends on

- [Gale–Stewart games for learning](gale-stewart-games.md)
- [Infinite Littlestone trees](infinite-littlestone-tree.md)

## Proof depends on

- [Gale–Stewart theorem, open case](../../../../../../SetTheory/determinacy/gale-stewart-games/determined-of-is-open.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483, Theorem A.1, Lemma 3.2, Definition 3.3 and Corollary 3.5 (with Theorem B.1).
