# Gale–Stewart games for learning

A **Gale–Stewart game** is an infinite two-player game of perfect information in which players $P_A$ and $P_L$ alternate moves $\xi_1, \eta_1, \xi_2, \eta_2, \dots$ with $\xi_t \in \mathcal{X}_t$ and $\eta_t \in \mathcal{Y}_t$ from fixed sets, and $P_L$ wins exactly when the play lies in a set $\mathbf{W}$ of infinite sequences that is **finitely decidable**: whenever a play lies in $\mathbf{W}$, some finite prefix of it already forces membership in $\mathbf{W}$ for every continuation. $P_A$ wins every play outside $\mathbf{W}$, that is, exactly when $P_L$ has not won after any finite number of rounds.

For a concept class $H \subseteq \{0,1\}^X$ and $x_1, y_1, \dots, x_t, y_t$ write $H_{x_1, y_1, \dots, x_t, y_t} = \{h \in H : h(x_i) = y_i \text{ for } i \le t\}$. In the **learning game** $\mathfrak{G}$, in each round $\tau$ the player $P_A$ chooses $\xi_\tau \in X$, then $P_L$ chooses $\eta_\tau \in \{0,1\}$; $P_L$ wins in round $\tau$ if $H_{\xi_1, \eta_1, \dots, \xi_\tau, \eta_\tau} = \emptyset$, and $P_A$ wins if this never happens. The winning set of $P_L$ is finitely decidable, so $\mathfrak{G}$ is a Gale–Stewart game. In the online-learning reading, $\eta_\tau$ is the label opposite to the learner's prediction at $\xi_\tau$: an adversary who keeps $H_{\xi_1, \eta_1, \dots, \xi_\tau, \eta_\tau}$ nonempty can force a mistake in every round.

## Depends on

- [Online classification protocol, mistakes and regret](../../../../online-learning-and-boosting/online-classification-protocol-mistakes-and-regret.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483, Section 3.2 and Appendix A.1.
