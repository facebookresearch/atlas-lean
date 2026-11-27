# No external regret implies no swap regret, and Littlestone games have correlated equilibria

Let the learner play distributions over an action set $X$ against reward functions from a class $F \subseteq [0,1]^X$ closed under convex combinations (otherwise replace $F$ by its convex hull). If some learner achieves external regret $o(T)$ against adaptive adversaries, then some learner achieves swap regret $o(T)$. In particular, if the reward functions are binary-valued ($F$ is the convex hull of a class of $\{0,1\}$-valued functions) and the class of functions indexed by the learner's actions has Littlestone dimension at most $L$, then swap regret at most $\varepsilon$ (normalized) is achievable after $T \ge (L/\varepsilon)^{O(1/\varepsilon)}$ rounds. For real-valued rewards the Littlestone dimension is replaced by the sequential fat-shattering dimension $\mathrm{SFat}(\cdot, \delta)$ of that class: if $\mathrm{SFat}(\cdot, \delta) = O(\delta^{-p})$ for some $p \in [0,2)$ and $I = \int_0^1 \sqrt{\mathrm{SFat}(\cdot, \delta)}\,d\delta$, then $T \ge (I/\varepsilon)^{O(1/\varepsilon)}$ rounds suffice. Consequently every game in which no-regret learning is possible has $\varepsilon$-approximate correlated equilibria for all $\varepsilon > 0$, including binary-valued games with infinite action sets of finite Littlestone dimension and real-valued games whose sequential fat-shattering dimension is finite at every scale, where even the existence of approximate correlated equilibria was previously unknown; this strengthens the classical fact that no-regret learning yields approximate coarse correlated equilibria.

## Proof sketch

Apply the tree lemma to the given external-regret learner: it needs only an external-regret guarantee over block-averaged losses, which holds for any learner whose regret bound is sublinear. For binary-valued Littlestone classes, agnostic online learning achieves external regret $O(\sqrt{LT\log T})$, so $M = \tilde O(L/\varepsilon^2)$; for real-valued classes the sequential Rademacher complexity, bounded by the entropy integral $I$ of the sequential fat-shattering dimension, plays the same role. Running no-swap-regret dynamics for all players yields empirical play converging to the set of approximate correlated equilibria.

## Depends on

- [Correlated equilibrium](../../../../GameTheory/noncooperative-games/correlated-equilibria/is-correlated-eq.md)
- [Swap regret](../../../../GameTheory/not-yet-classified/part-02/regret/swap-regret.md)
- [External regret](../../../../GameTheory/not-yet-classified/part-02/regret/external-regret.md)
- [The Littlestone dimension is the optimal mistake bound](../the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [Swap regret of the path mixture is controlled by external regret of the levels](treeswap-path-mixture-lemma.md)
- [Agnostic online learnability is characterized by the Littlestone dimension](../agnostic-online-learnability-is-characterized-by-the-littlestone-dimension.md)
- [No-swap-regret dynamics converge to correlated equilibria](../../../../GameTheory/noncooperative-games/no-regret-dynamics/no-swap-regret-dynamics-converge-to-correlated-equilibria.md)

## Sources

- Y. Dagan, C. Daskalakis, M. Fishelson, N. Golowich, "From External to Swap Regret 2.0: An Efficient Reduction for Large Action Spaces", STOC (2024), arXiv:2310.19786, Theorem 3.1, Corollaries 3.3, 3.4 and 3.6, Definition B.4 and Proposition B.5.
