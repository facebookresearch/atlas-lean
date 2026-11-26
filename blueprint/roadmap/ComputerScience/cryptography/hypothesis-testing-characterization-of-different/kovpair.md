# Kairouz–Oh–Viswanath tradeoff condition

Let $P, Q$ be probability mass functions on a finite type $\Omega$ and $\varepsilon, \delta \in \mathbb{R}$. The pair $(P, Q)$ satisfies the Kairouz–Oh–Viswanath condition with parameters $(\varepsilon, \delta)$ when, for every rejection set $S \subseteq \Omega$, the [type-I error](type-i.md) $\alpha = P(S)$ and [type-II error](type-ii.md) $\beta = Q(\Omega \setminus S)$ satisfy both

$$
\alpha + e^{\varepsilon} \beta \ge 1 - \delta \quad\text{and}\quad e^{\varepsilon} \alpha + \beta \ge 1 - \delta .
$$

## Sources

- P. Kairouz, S. Oh and P. Viswanath, *The Composition Theorem for Differential Privacy*, ICML 2015; IEEE Transactions on Information Theory, 2017; arXiv:1311.0776, Theorem 2.1, Eq. (1).
