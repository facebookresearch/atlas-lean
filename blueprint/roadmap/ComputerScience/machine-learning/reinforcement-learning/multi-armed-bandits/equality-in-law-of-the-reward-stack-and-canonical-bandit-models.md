# Equality in law of the reward-stack and canonical bandit models

Fix $k \ge 1$ arms, a finite horizon $n$, reward distributions $P_1, \dots, P_k$ on $\mathbb{R}$ and a
nonanticipating policy given by measurable kernels from past actions and rewards (and, if used,
independent internal randomization) to arms. In the reward-stack model, arm $i$ has an independent
sequence $(Y_{i,s})_{s \ge 1}$ of i.i.d. rewards with law $P_i$, independent across arms and of the
policy's randomization, and the $t$-th reward is $X_t = Y_{A_t, T_{A_t}(t)}$. Then the joint law of
$(A_1, X_1, \dots, A_n, X_n)$ in the reward-stack model equals the canonical law $\mathbb{P}_{\nu}$, so
the pull counts and every measurable functional of the history have the same law in the two models, and,
when the arms have finite means, the regret, which depends only on the law of the history, is the same in
the two models.

## Depends on

- [Reward-stack model of a stochastic bandit](reward-stack-model-of-a-stochastic-bandit.md)
- [Stochastic k-armed bandits: canonical history law](stochastic-k-armed-bandits-canonical-history-law-and-regret.md)
- [Pull count of an arm](canonical-bandit-model/pull-count.md)
- [Regret of a bandit policy](canonical-bandit-model/regret.md)
- [Bandits with finite means](canonical-bandit-model/has-finite-means.md)

## Proof depends on

- [Characterization of the canonical bandit model](canonical-bandit-model/map-eq-canonical-law-iff.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 4.6: conditions (a) and (b) on the interaction, Proposition 4.8 (any two probability spaces satisfying them give the same law of the history) and the reward-stack model; Exercise 4.4 asks for the equality of the random-table and stacked-reward laws. <https://tor-lattimore.com/downloads/book/book.pdf>
