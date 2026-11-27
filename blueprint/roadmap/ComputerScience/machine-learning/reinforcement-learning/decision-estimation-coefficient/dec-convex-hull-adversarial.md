# The DEC of the convex hull characterizes adversarial decision making

Consider the adversarial version of decision making with structured observations with a finite decision set $\Pi$: at each round $t \le T$ an adversary chooses a model $M_t \in \mathcal{M}$, the learner draws $\pi_t \sim p_t$ and observes $z_t = (r_t, o_t) \sim M_t(\pi_t)$, and the regret is $\mathrm{Reg} = \max_{\pi \in \Pi}\sum_{t=1}^T f^{M_t}(\pi) - \sum_{t=1}^T \mathbb{E}_{\pi \sim p_t}[f^{M_t}(\pi)]$. The upper and lower bounds below hold separately.

**Upper bound.** There is an algorithm (high-probability exploration by optimization) such that for every $\delta > 0$, against every, possibly adaptive, adversary, with probability at least $1 - \delta$,

$$
\mathrm{Reg} \le O(1)\cdot\inf_{\gamma > 0}\Big\{ \mathrm{dec}_\gamma\big(\mathrm{co}(\mathcal{M})\big)\cdot T + \gamma\log(|\Pi|/\delta) \Big\}.
$$

**Lower bound.** For a model $\bar M$ let $\mathcal{M}_\varepsilon(\bar M) = \{M \in \mathcal{M} : f^M(\pi_M) \le f^{\bar M}(\pi_{\bar M}) + \varepsilon\}$ be the alternatives whose optimal value exceeds that of $\bar M$ by at most $\varepsilon$, and define the localized coefficient $\mathrm{dec}_{\gamma,\varepsilon}(\mathcal{M}) = \sup_{\bar M \in \mathcal{M}} \mathrm{dec}_\gamma(\mathcal{M}_\varepsilon(\bar M), \bar M)$. Let $V(\mathcal{M}) \ge e$ bound the density ratios $M(E \mid \pi)/M'(E \mid \pi)$ over $M, M' \in \mathcal{M}$, decisions $\pi$ and events $E$, and suppose rewards are observed. There is a numerical constant $c > 0$ such that, with $C(T) = c\log(T \wedge V(\mathcal{M}))$ and $\varepsilon_\gamma = \gamma/(4C(T)T)$, for every algorithm there is an oblivious adversary under which

$$
\mathbb{E}[\mathrm{Reg}] + \sqrt{\mathbb{E}\big[(\mathrm{Reg})_+^2\big]} \;\ge\; \Omega(1)\cdot\sup_{\gamma > \sqrt{2C(T)T}} \mathrm{dec}_{\gamma,\varepsilon_\gamma}\big(\mathrm{co}(\mathcal{M})\big)\cdot T - O(\sqrt{T}),
$$

where $x_+ = \max\{x, 0\}$. Consequently, an algorithm that is sub-Chebyshev with parameter $R$, meaning $\Pr(\mathrm{Reg}_+ \ge t) \le R^2/t^2$ for all $t > 0$, has $R \ge \tilde\Omega(1)\cdot\sup_{\gamma > \sqrt{2C(T)T}} \mathrm{dec}_{\gamma,\varepsilon_\gamma}(\mathrm{co}(\mathcal{M}))\cdot T - O(\sqrt T)$. The lower bound controls the first two moments of regret through the localized coefficient, not the expected regret through the unrestricted one, so the two bounds match only up to localization, the dependence on $\log|\Pi|$, and logarithmic factors. Up to a factor of $4$ in $\gamma$, $\mathrm{dec}_\gamma(\mathrm{co}(\mathcal{M}))$ also equals the minimax value of the high-probability exploration-by-optimization objective of Lattimore and György.

## Proof sketch

For the upper bound, each round runs exponential weights on importance-weighted reward estimates to get a reference distribution over decisions and then solves the min-max exploration-by-optimization problem for the sampling distribution and the estimator; a variational characterization of squared Hellinger distance through moment generating functions shows that this problem's value lies between $\mathrm{dec}_{1/(4\eta)}(\mathrm{co}(\mathcal{M}))$ and $\mathrm{dec}_{1/(8\eta)}(\mathrm{co}(\mathcal{M}))$ for learning rate $\eta$, and the exponential-weights analysis gives the bound with the additive $\gamma\log(|\Pi|/\delta)$ term. For the lower bound, an oblivious adversary that draws $M_t$ i.i.d. from a fixed mixture $\bar M \in \mathrm{co}(\mathcal{M})$ realizes $\bar M$ as a stochastic environment, so a change-of-measure argument for the stochastic localized lower bound, applied to $\mathrm{co}(\mathcal{M})$, transfers.

## Depends on

- [Decision-estimation coefficient](decision-estimation-coefficient.md)

## Proof depends on

- [Estimation-to-decisions regret is bounded by the DEC plus the estimation error](e2d-regret-upper-bound.md)
- [The constrained DEC lower bounds the regret of every algorithm](dec-regret-lower-bound.md)
- [Regret of Exp3 for adversarial bandits](../multi-armed-bandits/regret-of-exp3-for-adversarial-bandits.md)

## Sources

- D. J. Foster, A. Rakhlin, A. Sekhari, K. Sridharan, "On the Complexity of Adversarial Decision Making", NeurIPS (2022), arXiv:2206.13063, Section 2 (Theorem 2.1, Eqs. (10)–(11) and (13); Theorem 2.2, Eq. (15); Definition 2.1 and Corollary 2.1).
