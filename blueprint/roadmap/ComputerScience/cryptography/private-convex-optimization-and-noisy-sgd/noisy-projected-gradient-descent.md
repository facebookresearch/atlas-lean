# Privacy and utility of noisy projected gradient descent

Under the assumptions of private ERM, consider noisy projected gradient descent $w_{t+1} = \Pi_{\mathcal{W}}\big(w_t - \eta(\nabla\hat F_S(w_t) + \xi_t)\big)$, $\xi_t \sim \mathcal{N}(0, \sigma^2 I_d)$, for $T$ steps, outputting the average iterate. Each step is a Gaussian mechanism on a gradient of $\ell_2$-sensitivity $2L/n$, so with

$$
\sigma = \frac{2L\sqrt{T}}{n\sqrt{2\rho}}, \qquad \rho + 2\sqrt{\rho\log(1/\delta)} = \varepsilon, \qquad \text{so that } \sigma = O\Big(\frac{L\sqrt{T\log(1/\delta)}}{n\varepsilon}\Big) \text{ for } \varepsilon \le \log(1/\delta),
$$

(by zCDP composition) the algorithm is $(\varepsilon,\delta)$-differentially private, and with step size $\eta = D/\sqrt{T(L^2 + d\sigma^2)}$ its expected excess empirical risk is $O\big(D\sqrt{(L^2 + d\sigma^2)/T}\big) = O\big(LD/\sqrt{T} + LD\sqrt{d\log(1/\delta)}/(\varepsilon n)\big)$, which with $T \gtrsim (\varepsilon n)^2/(d\log(1/\delta))$ gives the optimal private ERM rate.

## Proof sketch

Privacy: each step is $2L^2/(n^2\sigma^2)$-zCDP, so $T$ steps are $2TL^2/(n^2\sigma^2)$-zCDP, which converts to $(\varepsilon,\delta)$-DP for the stated $\sigma$. Utility: projected stochastic gradient descent with unbiased gradient estimates of second moment at most $L^2 + d\sigma^2$ has average-iterate suboptimality $D\sqrt{L^2 + d\sigma^2}/\sqrt{T}$ by the standard online convex optimization regret bound.

## Depends on

- [Private empirical risk minimization and private stochastic convex optimization](private-erm-and-sco.md)

## Proof depends on

- [Conversion from zCDP to approximate differential privacy](../zero-concentrated-differential-privacy/zcdp-to-approximate-dp.md)
- [The Gaussian mechanism satisfies zCDP with parameter sensitivity squared over twice the variance](../zero-concentrated-differential-privacy/gaussian-mechanism-zcdp.md)
- [Regularized Follow-the-Leader / Online Mirror Descent regret](../../machine-learning/online-learning-and-boosting/regularized-follow-the-leader-online-mirror-descent-regret.md)

## Sources

- R. Bassily, A. Smith, A. Thakurta, "Differentially Private Empirical Risk Minimization: Efficient Algorithms and Tight Error Bounds", FOCS (2014), arXiv:1405.7085.
- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065.
