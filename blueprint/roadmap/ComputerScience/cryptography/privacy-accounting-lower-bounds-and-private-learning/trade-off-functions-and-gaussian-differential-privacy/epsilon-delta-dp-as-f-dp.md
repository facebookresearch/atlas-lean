# Approximate differential privacy as f-differential privacy

For $\varepsilon \ge 0$ and $\delta \in [0,1]$ consider the function $f_{\varepsilon,\delta}$ (defined, for all real parameters, as the tradeoff lower bound of approximate differential privacy):

$$
f_{\varepsilon, \delta}(\alpha) = \max\big\{0,\; 1 - \delta - e^{\varepsilon}\alpha,\; e^{-\varepsilon}(1 - \delta - \alpha)\big\}.
$$

Then, for output distributions on an arbitrary measurable space, a mechanism is $(\varepsilon,\delta)$-differentially private if and only if it is $f_{\varepsilon,\delta}$-DP; this measurable-space equivalence is broader than the corresponding results for finitely supported output distributions. In particular $(\varepsilon,0)$-DP corresponds to the piecewise linear trade-off function with slopes $-e^{\varepsilon}$ and $-e^{-\varepsilon}$, and $f_{\varepsilon,\delta}$ is the trade-off function of a pair of distributions on a four-point space.

## Proof sketch

$(\varepsilon,\delta)$-DP says $\mathbb{E}_{M(S)}[\phi] \le e^{\varepsilon}\mathbb{E}_{M(S')}[\phi] + \delta$ for indicator, hence by linearity for all $[0,1]$-valued, rejection rules, applied to both $\phi$ and $1 - \phi$ and with the roles of $S, S'$ exchanged. Rewriting these two inequalities in terms of $\alpha_\phi$ and $\beta_\phi$ gives exactly $\beta_\phi \ge 1 - \delta - e^{\varepsilon}\alpha_\phi$ and $\beta_\phi \ge e^{-\varepsilon}(1 - \delta - \alpha_\phi)$, that is, $T \ge f_{\varepsilon,\delta}$; the converse reverses the computation.

## Depends on

- [f-differential privacy](f-differential-privacy.md)
- [Tradeoff lower bound of approximate differential privacy](../../hypothesis-testing-characterization-of-different/f-eps-delta.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
- P. Kairouz, S. Oh, P. Viswanath, "The Composition Theorem for Differential Privacy", ICML (2015); IEEE Transactions on Information Theory 63 (2017), arXiv:1311.0776.
