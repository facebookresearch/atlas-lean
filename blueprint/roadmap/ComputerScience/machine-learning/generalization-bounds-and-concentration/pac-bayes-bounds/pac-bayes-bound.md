# PAC-Bayes bound (McAllester form)

Let $\ell : H \times Z \to [0,1]$ be measurable, let $P$ be a prior distribution on $H$ chosen before the sample, let
$m \ge 2$ be an integer and $\delta \in (0,1)$. With probability at least $1 - \delta$ over $S \sim D^m$, simultaneously for
every posterior $Q$ on $H$ (which may depend on $S$),

$$L_D(Q) \le L_S(Q) + \sqrt{\frac{\mathrm{KL}(Q \Vert P) + \ln(m/\delta)}{2(m-1)}},$$

where $L(Q) = \mathbb{E}_{h \sim Q} L(h)$; when $\mathrm{KL}(Q \Vert P) = \infty$ the bound is vacuous (Shalev-Shwartz and
Ben-David, Theorem 31.1).

## Expansion

This node states a precise result. A good expansion adds a page for the pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: relative entropy of probability measures on a general space.

## Depends on

- [Expected risk](../risk.md)
- [Empirical risk](../empirical-risk.md)

## Related topics

- [Catoni's PAC-Bayes bound](catoni-pac-bayes.md)

## Sources

- Understanding Machine Learning: From Theory to Algorithms — Shalev-Shwartz, Ben-David / Cambridge University Press, Theorem 31.1. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
