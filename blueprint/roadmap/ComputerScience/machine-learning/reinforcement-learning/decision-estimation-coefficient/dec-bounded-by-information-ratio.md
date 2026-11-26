# The DEC of the convex hull is bounded by the information ratio

Let $\Pi$ be finite and let $\mathcal{M}$ be a model class with rewards in $[0,1]$. For a prior $\mu \in \Delta(\mathcal{M} \times \Pi)$ on **model–comparator pairs** $(M, \pi^\star)$ and a decision distribution $p \in \Delta(\Pi)$, let $\mathbb{P}$ be the law of $(M, \pi^\star) \sim \mu$, $\pi \sim p$, $z \sim M(\pi)$, and let $\mu^{\mathrm{pr}}(\pi') = \mathbb{P}(\pi^\star = \pi')$ and $\mu^{\mathrm{po}}(\pi'; \pi, z) = \mathbb{P}(\pi^\star = \pi' \mid \pi, z)$ be the prior and posterior laws of the comparator. The **parameterized information ratio** with squared Hellinger distance is

$$
\mathrm{inf}^{H}_{\gamma}(\mathcal{M}) = \sup_{\mu \in \Delta(\mathcal{M} \times \Pi)} \inf_{p \in \Delta(\Pi)} \Big\{ \mathbb{E}_{\pi \sim p}\mathbb{E}_{(M, \pi^\star) \sim \mu}\big[f^M(\pi^\star) - f^M(\pi)\big] - \gamma\,\mathbb{E}_{\pi \sim p}\mathbb{E}_{z \mid \pi}\big[D_H^2\big(\mu^{\mathrm{po}}(\cdot; \pi, z), \mu^{\mathrm{pr}}\big)\big] \Big\},
$$

so the information term measures how much observing $(\pi, z)$ updates the law of the comparator. Then for all $\gamma > 0$,

$$
\mathrm{inf}^{H}_{\gamma}(\mathcal{M}) \;\le\; \mathrm{dec}_\gamma\big(\mathrm{co}(\mathcal{M})\big) \;\le\; \mathrm{inf}^{H}_{\gamma/4}(\mathcal{M}).
$$

In particular, if the generalized information ratio $\Psi(\mathcal{M}) = \sup_{\mu} \inf_{p} \big(\mathbb{E}_{(M,\pi^\star) \sim \mu}\mathbb{E}_{\pi \sim p}[f^M(\pi^\star) - f^M(\pi)]\big)^2 / \mathbb{E}_{\pi \sim p}\mathbb{E}_{z \mid \pi}[D_H^2(\mu^{\mathrm{po}}(\cdot; \pi, z), \mu^{\mathrm{pr}})]$ is finite, then $\mathrm{inf}^H_\gamma(\mathcal{M}) \le \Psi(\mathcal{M})/\gamma$, and hence $\mathrm{dec}_\gamma(\mathrm{co}(\mathcal{M})) \le 4\Psi(\mathcal{M})/\gamma$ for all $\gamma > 0$. The parameterized information ratio is invariant under convexification, $\mathrm{inf}^H_\gamma(\mathrm{co}(\mathcal{M})) = \mathrm{inf}^H_\gamma(\mathcal{M})$.

## Proof sketch

For the upper bound, fix a reference model; by the minimax theorem (with $\Pi$ finite and rewards bounded) the DEC of the convex hull is a supremum over mixtures $\nu \in \Delta(\mathcal{M})$, and $\nu$ induces a prior $\mu$ on pairs $(M, \pi_M)$. Convexity of the squared Hellinger distance replaces each model by the conditional mixture given the comparator, the triangle inequality for Hellinger distance (costing the factor $4$) replaces the reference by the overall mixture, and Bayes' rule turns the Hellinger distance between observation laws into the Hellinger distance between posterior and prior laws of the comparator. Choosing $p$ optimal for $\mu$ in the information ratio at parameter $\gamma/4$ gives the upper inequality; the lower one runs the same identities in reverse. For the consequence, a $p$ nearly attaining the ratio for $\mu$ has regret at most $\sqrt{\Psi x}$, where $x$ is its information term, and $\sqrt{\Psi x} \le \Psi/(4\gamma) + \gamma x \le \Psi/\gamma + \gamma x$.

## Depends on

- [Decision-estimation coefficient](decision-estimation-coefficient.md)
- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Proof depends on

- [The DEC of the convex hull characterizes adversarial decision making](dec-convex-hull-adversarial.md)
- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- D. J. Foster, A. Rakhlin, A. Sekhari, K. Sridharan, "On the Complexity of Adversarial Decision Making", NeurIPS (2022), arXiv:2206.13063, Section 3 (Eq. (20), Definition 3.1, Theorem 3.1, Proposition 3.1) and Appendix C (Proposition C.1, Theorem C.1).
- D. Russo, B. Van Roy, "Learning to Optimize via Posterior Sampling", Mathematics of Operations Research 39 (2014), arXiv:1301.2609.
