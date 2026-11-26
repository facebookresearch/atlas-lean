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

For the upper bound, first let $\mathcal{M}'$ be an arbitrary model class and fix a reference model $\bar M$. By the minimax theorem (with $\Pi$ finite and rewards bounded; if needed, replace $\bar M$ by a nearby reference with bounded divergences, at an arbitrarily small additive cost) the DEC of $\mathcal{M}'$ at $\bar M$ is at most $\sup_{\nu \in \Delta(\mathcal{M}')} \inf_p \mathbb{E}_{M \sim \nu}\mathbb{E}_{\pi \sim p}[f^M(\pi_M) - f^M(\pi) - \gamma D_H^2(M(\pi), \bar M(\pi))]$, and $\nu$ induces a prior $\mu \in \Delta(\mathcal{M}' \times \Pi)$ on pairs $(M, \pi_M)$. Convexity of the squared Hellinger distance in its first argument replaces each model by the conditional mixture $M_{\pi^\star} = \mathbb{E}_\mu[M \mid \pi^\star]$, and the triangle inequality for the Hellinger distance (costing the factor $4$) replaces the reference by the overall mixture $\mathbb{E}_\mu[M]$. Bayes' rule, using that $\pi$ and $\pi^\star$ are independent, turns $\mathbb{E}_{\pi^\star} D_H^2(M_{\pi^\star}(\pi), \mathbb{E}_\mu[M](\pi))$ into $\mathbb{E}_{z \mid \pi} D_H^2(\mu^{\mathrm{po}}(\cdot; \pi, z), \mu^{\mathrm{pr}})$. Choosing $p$ optimal for $\mu$ in the information ratio at parameter $\gamma/4$ gives $\mathrm{dec}_\gamma(\mathcal{M}') \le \mathrm{inf}^H_{\gamma/4}(\mathcal{M}')$. Apply this to $\mathcal{M}' = \mathrm{co}(\mathcal{M})$ and use convexification invariance: representing each model of $\mathrm{co}(\mathcal{M})$ as a mixture over $\mathcal{M}$ and sampling a model from that mixture leaves the joint law of $(\pi, \pi^\star, z)$, the expected regret and the comparator prior and posterior unchanged, so $\mathrm{inf}^H_{\gamma/4}(\mathrm{co}(\mathcal{M})) = \mathrm{inf}^H_{\gamma/4}(\mathcal{M})$.

For the lower bound, fix $\mu \in \Delta(\mathcal{M} \times \Pi)$ and let $M_{\pi'} = \mathbb{E}_\mu[M \mid \pi^\star = \pi']$ be the model conditional on the comparator and $\bar M = \mathbb{E}_\mu[M]$; both lie in $\mathrm{co}(\mathcal{M})$. By Bayes' rule the information term equals $\mathbb{E}_{\pi \sim p}\mathbb{E}_{\pi^\star \sim \mu^{\mathrm{pr}}} D_H^2(M_{\pi^\star}(\pi), \bar M(\pi))$, and the expected regret is at most $\mathbb{E}_{\pi^\star}\mathbb{E}_{\pi \sim p}[\max_{\pi'} f^{M_{\pi^\star}}(\pi') - f^{M_{\pi^\star}}(\pi)]$. Taking $p$ from the definition of $\mathrm{dec}_\gamma(\mathrm{co}(\mathcal{M}))$ at the reference $\bar M$, each conditional model $M_{\pi^\star}$ has gap minus $\gamma$ times its Hellinger divergence from $\bar M$ at most $\mathrm{dec}_\gamma(\mathrm{co}(\mathcal{M}))$; averaging over $\pi^\star$ gives the lower inequality. For the consequence, a $p$ nearly attaining the ratio for $\mu$ has regret at most $\sqrt{\Psi x}$, where $x$ is its information term, and $\sqrt{\Psi x} \le \Psi/(4\gamma) + \gamma x \le \Psi/\gamma + \gamma x$.

## Depends on

- [Decision-estimation coefficient](decision-estimation-coefficient.md)
- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Proof depends on

- [The DEC of the convex hull characterizes adversarial decision making](dec-convex-hull-adversarial.md)
- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- D. J. Foster, A. Rakhlin, A. Sekhari, K. Sridharan, "On the Complexity of Adversarial Decision Making", NeurIPS (2022), arXiv:2206.13063, Section 3 (Eq. (20), Definition 3.1, Theorem 3.1, Proposition 3.1) and Appendix C (Proposition C.1, Theorem C.1).
- D. Russo, B. Van Roy, "Learning to Optimize via Posterior Sampling", Mathematics of Operations Research 39 (2014), arXiv:1301.2609.
