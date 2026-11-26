# The DEC of the convex hull characterizes adversarial decision making

In the adversarial version of decision making with structured observations, where at each round an adversary chooses the model $M_t \in \mathcal{M}$ (adversarial rewards or dynamics) and regret is measured against the best fixed decision $\max_\pi \sum_t f^{M_t}(\pi)$, the minimax regret is characterized, up to logarithmic factors and the estimation term, by the DEC of the convex hull:

$$
T\cdot\mathrm{dec}_{\gamma}\big(\mathrm{co}(\mathcal{M})\big) \;\lesssim\; \text{minimax regret} \;\lesssim\; \inf_{\gamma > 0}\Big\{ T\cdot\mathrm{dec}_\gamma\big(\mathrm{co}(\mathcal{M})\big) + \gamma\log|\Pi| \Big\},
$$

for appropriate $\gamma$ in the lower bound. Thus the price of adversarial rewards or dynamics is governed by convexification of the model class. The DEC of the convex hull is bounded by the information ratio of Russo and Van Roy and is equivalent to the exploration-by-optimization objective of Lattimore and György.

## Proof sketch

For the upper bound, run exponential weights over decisions as the estimation oracle on the convex hull: mixtures of adversarial models are the natural estimates, and the regret decomposition of E2D holds with $\log|\Pi|$ as estimation error. For the lower bound, an adversary sampling models from a mixture realizes any element of the convex hull in expectation, so the stochastic lower bound applied to $\mathrm{co}(\mathcal{M})$ transfers. The information-ratio comparison follows by choosing $p$ as the information-directed sampling distribution in the DEC.

## Depends on

- [Estimation-to-decisions regret is bounded by the DEC plus the estimation error](e2d-regret-upper-bound.md)
- [The localized DEC lower bounds the regret of every algorithm](dec-regret-lower-bound.md)
- [Regret of Exp3 for adversarial bandits](../multi-armed-bandits/regret-of-exp3-for-adversarial-bandits.md)

## Proof depends on

- [Estimation-to-decisions regret is bounded by the DEC plus the estimation error](e2d-regret-upper-bound.md)
- [The localized DEC lower bounds the regret of every algorithm](dec-regret-lower-bound.md)
- [Regret of Exp3 for adversarial bandits](../multi-armed-bandits/regret-of-exp3-for-adversarial-bandits.md)

## Sources

- D. J. Foster, A. Rakhlin, A. Sekhari, K. Sridharan, "On the Complexity of Adversarial Decision Making", NeurIPS (2022), arXiv:2206.13063.
