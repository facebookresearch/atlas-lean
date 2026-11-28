# Variance linear combination

Let $(\Omega, \mu)$ be a probability space, $X : \Omega \to \mathbb{R}^m$ a random vector whose coordinates $X_a$ all lie in $L^2(\mu)$, and $w \in \mathbb{R}^m$. Then the variance of the linear combination $\sum_a w_a X_a$ is the quadratic form of $w$ in the covariance matrix:

$$\operatorname{Var}\Bigl(\sum_{a=1}^{m} w_a X_a\Bigr) = \sum_{a=1}^{m} \sum_{b=1}^{m} w_a w_b \operatorname{Cov}(X_a, X_b).$$
