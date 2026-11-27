# Event-form approximate differential privacy as a tradeoff condition

Let $M$ be a mechanism with values in probability mass functions on a finite type, $\mathrm{adj}$ a symmetric relation, and $\varepsilon \ge 0$, $\delta \ge 0$. Then $M$ is [$(\varepsilon, \delta)$-differentially private](../approximate-differential-privacy/is-approx-dp.md) for $\mathrm{adj}$ if and only if $(M(d), M(d'))$ satisfies the [Kairouz–Oh–Viswanath condition](kovpair.md) with parameters $(\varepsilon, \delta)$ for every pair with $\mathrm{adj}(d, d')$.

## Sources

- P. Kairouz, S. Oh and P. Viswanath, *The Composition Theorem for Differential Privacy*, ICML 2015; IEEE Transactions on Information Theory, 2017; arXiv:1311.0776, Theorem 2.1.
