# The DEC of the convex hull is bounded by the information ratio

Suppose that for every prior $\mu$ over $\mathcal{M}$ there is a decision distribution $p$ such that the Bayesian information ratio satisfies $\big(\mathbb{E}_{M \sim \mu}\mathbb{E}_{\pi \sim p}[f^M(\pi_M) - f^M(\pi)]\big)^2 \le \Psi \cdot \mathbb{E}_{M \sim \mu}\mathbb{E}_{\pi \sim p}\big[D_H^2(M(\pi), \bar M_\mu(\pi))\big]$, where $\bar M_\mu = \mathbb{E}_{M \sim \mu}[M]$ is the posterior mean model (a Hellinger form of the information ratio). Then $\mathrm{dec}_\gamma(\mathrm{co}(\mathcal{M})) \le \Psi/(4\gamma)$ for all $\gamma > 0$. Consequently information-ratio bounds for bandit problems (for example $\Psi \le K$ for $K$-armed bandits and $\Psi \le d$ for linear bandits) translate into DEC bounds and regret bounds for both stochastic and adversarial decision making.

## Proof sketch

By the minimax theorem, $\mathrm{dec}_\gamma(\mathrm{co}(\mathcal{M}), \bar M)$ equals a supremum over priors of a Bayesian quantity in which the reference model is the posterior mean; choosing $p$ from the information-ratio assumption gives regret $\le \sqrt{\Psi \cdot \mathrm{Info}}$, and the AM–GM inequality $\sqrt{\Psi x} \le \Psi/(4\gamma) + \gamma x$ cancels the information term against the Hellinger penalty.

## Depends on

- [The DEC of the convex hull characterizes adversarial decision making](dec-convex-hull-adversarial.md)
- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Proof depends on

- [The DEC of the convex hull characterizes adversarial decision making](dec-convex-hull-adversarial.md)
- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- D. J. Foster, A. Rakhlin, A. Sekhari, K. Sridharan, "On the Complexity of Adversarial Decision Making", NeurIPS (2022), arXiv:2206.13063.
- D. Russo, B. Van Roy, "Learning to Optimize via Posterior Sampling", Mathematics of Operations Research 39 (2014), arXiv:1301.2609.
