# Expectation of the Mann–Whitney statistic

Let $\mu_X$ and $\mu_Y$ be probability measures on $\mathbb{R}$, and let $X_1, \dots, X_m, Y_1, \dots, Y_n$ be independent random variables on a probability space $(\Omega, \mu)$ with each $X_i$ of law $\mu_X$ and each $Y_j$ of law $\mu_Y$. Let

$$U = \sum_{i=1}^{m} \sum_{j=1}^{n} \Big(\mathbf 1[Y_j < X_i] + \tfrac12\, \mathbf 1[Y_j = X_i]\Big)$$

be the Mann–Whitney statistic, with ties counted one half. Then

$$\mathbb{E}[U] = mn \int\!\!\int k(a,b)\, d\mu_Y(b)\, d\mu_X(a) = mn\Big(P(Y < X) + \tfrac12 P(Y = X)\Big),$$

where $k(a,b) = \mathbf 1[b < a] + \tfrac12 \mathbf 1[b = a]$ and $X \sim \mu_X$, $Y \sim \mu_Y$ are independent.
