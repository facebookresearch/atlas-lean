# Privacy and utility of noisy projected gradient descent

Under the assumptions of private ERM (in particular $\mathcal{W}$ nonempty, closed, convex and bounded, so that the projection $\Pi_{\mathcal{W}}$ and an empirical minimizer exist), fix for every $w$ and $z$ a subgradient $g(w, z) \in \partial_w \ell(w, z)$, chosen by a fixed rule independent of the data, with $\lVert g(w, z) \rVert_2 \le L$ (such subgradients exist by $L$-Lipschitzness; for differentiable losses take the gradient). Consider noisy projected gradient descent $w_{t+1} = \Pi_{\mathcal{W}}\big(w_t - \eta(\bar g_S(w_t) + \xi_t)\big)$ with $\bar g_S(w) = \frac1n\sum_i g(w, z_i)$ and $\xi_t \sim \mathcal{N}(0, \sigma^2 I_d)$, for $T$ steps, outputting the average iterate. For datasets differing in one element, $\bar g_S(w)$ changes by at most $2L/n$ in $\ell_2$ norm, so each step is a Gaussian mechanism on a quantity of $\ell_2$-sensitivity $2L/n$, and with

$$
\sigma = \frac{2L\sqrt{T}}{n\sqrt{2\rho}}, \qquad \rho + 2\sqrt{\rho\log(1/\delta)} = \varepsilon, \qquad \text{so that } \sigma = O\Big(\frac{L\sqrt{T\log(1/\delta)}}{n\varepsilon}\Big) \text{ for } \varepsilon \le \log(1/\delta),
$$

(by zCDP composition) the algorithm is $(\varepsilon,\delta)$-differentially private, and with step size $\eta = D/\sqrt{T(L^2 + d\sigma^2)}$ its expected excess empirical risk is $O\big(D\sqrt{(L^2 + d\sigma^2)/T}\big) = O\big(LD/\sqrt{T} + LD\sqrt{d\log(1/\delta)}/(\varepsilon n)\big)$, which with $T \gtrsim (\varepsilon n)^2/(d\log(1/\delta))$ is $O\big(LD\sqrt{d\log(1/\delta)}/(\varepsilon n)\big)$. This is a utility upper bound only, not an optimality claim: for very small $\delta$ it can be worse than what a pure $\varepsilon$-differentially private algorithm achieves (for $d = \varepsilon = 1$ and $\delta = e^{-n^2}$ it is of order $LD$, while pure private ERM attains $O(LD/n)$).

## Proof sketch

Privacy: each step is $2L^2/(n^2\sigma^2)$-zCDP, so $T$ steps are $2TL^2/(n^2\sigma^2)$-zCDP, which converts to $(\varepsilon,\delta)$-DP for the stated $\sigma$. Utility: $\bar g_S(w_t) + \xi_t$ is an unbiased estimate of a subgradient of $\hat F_S$ at $w_t$, and projected stochastic subgradient descent with unbiased subgradient estimates of second moment at most $L^2 + d\sigma^2$ has average-iterate suboptimality $D\sqrt{L^2 + d\sigma^2}/\sqrt{T}$ by the standard online convex optimization regret bound.

## Depends on

- [Private empirical risk minimization and private stochastic convex optimization](private-erm-and-sco.md)

## Proof depends on

- [Conversion from zCDP to approximate differential privacy](../zero-concentrated-differential-privacy/zcdp-to-approximate-dp.md)
- [The Gaussian mechanism satisfies zCDP with parameter sensitivity squared over twice the variance](../zero-concentrated-differential-privacy/gaussian-mechanism-zcdp.md)
- [Regularized Follow-the-Leader / Online Mirror Descent regret](../../../machine-learning/online-learning-and-boosting/regularized-follow-the-leader-online-mirror-descent-regret.md)

## Sources

- R. Bassily, A. Smith, A. Thakurta, "Differentially Private Empirical Risk Minimization: Efficient Algorithms and Tight Error Bounds", FOCS (2014), arXiv:1405.7085.
- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065.
