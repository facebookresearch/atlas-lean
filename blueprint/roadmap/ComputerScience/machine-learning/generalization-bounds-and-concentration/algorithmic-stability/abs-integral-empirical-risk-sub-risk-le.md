# Uniform stability implies generalization in expectation

Let $\nu$ be a probability measure on the example space $\mathcal{Z}$, let $S = (z_1, \dots, z_n) \sim \nu^{\otimes n}$ with $n \ge 1$, and let $A$ be an [$\varepsilon$-uniformly stable](is-uniformly-stable.md) algorithm for a loss $L$. Assume that $(S, z) \mapsto L(A(S), z)$ is jointly measurable and bounded. Then

$$
\Big\lvert\, \mathbb{E}_S\big[\hat R_S(A(S)) - R(A(S))\big] \Big\rvert \le \varepsilon,
$$

where $\hat R_S(h) = \frac1n \sum_{i=1}^n L(h, z_i)$ is the [empirical risk](../empirical-risk.md) and $R(h) = \mathbb{E}_{z \sim \nu} L(h, z)$ the [expected risk](../risk.md).

Proof: by [replace-one sampling](map-update-prod-pi.md), $\mathbb{E}\, L(A(S), z_i) = \mathbb{E}\, L(A(S^{(i, z)}), z)$ for an independent $z \sim \nu$, while $\mathbb{E}\, R(A(S)) = \mathbb{E}\, L(A(S), z)$ by Fubini. Each of the $n$ differences $L(A(S^{(i, z)}), z) - L(A(S), z)$ lies in $[-\varepsilon, \varepsilon]$ by stability, and averaging over $i$ gives the bound.

The source states the theorem without regularity hypotheses. Joint measurability makes the loss at a training example, $S \mapsto L(A(S), z_i)$, measurable, and boundedness makes every expectation in the proof finite; both are added here. The bound holds in expectation only.

Unlike the [uniform deviation bounds](../measure-real-exists-abs-empirical-risk-s.md) of the parent topic and [Rademacher complexity](../rademacher-complexity/README.md), the bound involves no complexity of a class of predictors: only the sensitivity of the algorithm to one example. Combined with [the uniform stability of stochastic gradient descent](integral-abs-sgm-output-sub-le.md), it bounds the [generalization gap of SGD](abs-integral-empirical-risk-sub-risk-sgm.md) by $2L^2/n$ times the sum of its step sizes, for a loss bounded at the starting point.

## Sources

- M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Theorem 2.2 (proof via a ghost sample $S'$ and the replace-one samples $S^{(i)}$; the source attributes the argument to Lemma 7 of Bousquet and Elisseeff).
- O. Bousquet and A. Elisseeff, *Stability and generalization*, Journal of Machine Learning Research 2 (2002), 499–526.
