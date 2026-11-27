# Gale–Stewart games for learning

A **Gale–Stewart game** is an infinite two-player game of perfect information in which players $P_A$ and $P_L$ alternate moves $\xi_1, \eta_1, \xi_2, \eta_2, \dots$ from fixed sets, and the winner is determined by membership of the play in a set $W$ of infinite sequences. The game is **open** for $P_L$ if $P_L$ wins exactly when some finite prefix of the play lies in a fixed set of finite sequences (so a win, once reached, is decided at a finite time).

In the universal-learning reduction, $P_A$ (the adversary) plays $\xi_t = x_t \in X$, $P_L$ (the learner) plays $\eta_t \in \{0,1\}$, then $P_A$ reveals $y_t \ne \eta_t$; the adversary must keep $(x_1,y_1), \dots, (x_t,y_t)$ realizable by $H$. The learner wins as soon as the adversary can no longer continue, that is, when the labelled sequence leaves the set of realizable finite samples.

## Depends on

- [Infinite Littlestone trees](infinite-littlestone-tree.md)
- [Online classification protocol, mistakes and regret](../../../../online-learning-and-boosting/online-classification-protocol-mistakes-and-regret.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483.
