# Pointwise Hoeffding bound for the empirical distribution function

Let $X_1, \dots, X_n$ be independent random variables on a probability space $(\Omega, \mu)$, each with law $\nu$, a probability measure on $\mathbb{R}$. Assume $n \ge 1$ and let $F_n$ be the empirical distribution function of $X_1, \dots, X_n$ and $F(x) = \nu((-\infty, x])$. Then for every $x \in \mathbb{R}$ and $\varepsilon > 0$

$$\mu\big(|F_n(x) - F(x)| > \varepsilon\big) \le 2 e^{-2n\varepsilon^2}.$$
