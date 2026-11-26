# Conditional channel law

Let $(\Omega, \mu)$ be a probability space and $X, Z : \Omega \to \mathbb{R}$ measurable and independent, with $Z \sim \mathcal{N}(0, N)$ for some $N > 0$. Let $e : \mathbb{R} \to \mathbb{R}^1$, $e(x) = (x)$, be the scalar coordinate embedding into the one-dimensional Euclidean space, a linear isometry with inverse $e^{-1}(y) = y_0$. Then the conditional distribution of $e(X + Z)$ given $e(X)$ agrees, for almost every value $y$ of $e(X)$ under its law, with the additive-noise kernel at gain $[1]$ and noise covariance $[N]$, which sends $y \in \mathbb{R}^1$ to the law of $y + W$ with $W \sim \mathcal{N}(0, [N])$:

$$P_{e(X+Z) \mid e(X) = y} = \mathcal{N}\big(y, [N]\big).$$
