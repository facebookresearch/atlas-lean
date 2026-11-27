# No infinite Littlestone tree gives an online learner with finitely many mistakes

Let $H \subseteq \{0,1\}^X$ have no infinite Littlestone tree. Then there is an online learner $\hat y_t = \hat y_t(x_1, y_1, \dots, x_{t-1}, y_{t-1}, x_t)$ such that for every sequence $(x_t, y_t)_{t \ge 1}$ all of whose finite prefixes are realizable by $H$, the learner makes only finitely many mistakes: $\#\{t : \hat y_t \ne y_t\} < \infty$. The number of mistakes need not be bounded uniformly over sequences (this would require finite Littlestone dimension).

## Proof sketch

By Gale–Stewart determinacy the learner has a winning strategy in the learning game. Run it, but only update its state on rounds where it errs: every mistake is a move of the adversary in the game, and a winning strategy guarantees that after finitely many such moves the realizable continuation ceases to exist. Since the actual sequence is realizable along every prefix, the game cannot be continued forever, so the number of mistake rounds is finite.

## Depends on

- [Online classification protocol, mistakes and regret](../../../../online-learning-and-boosting/online-classification-protocol-mistakes-and-regret.md)
- [Infinite Littlestone trees](infinite-littlestone-tree.md)

## Proof depends on

- [The learning game is determined, and the adversary wins exactly on an infinite Littlestone tree](gale-stewart-determinacy.md)
- [Gale–Stewart games for learning](gale-stewart-games.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483, Section 3.1 (Theorem 3.1) and Section 3.2.
