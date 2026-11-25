# Covariance linear map

Let $(\Omega, \mu)$ be a probability space, $X : \Omega \to \mathbb{R}^m$ a random vector whose coordinates $X_a$ all lie in $L^2(\mu)$, and $J$ a deterministic real $p \times m$ matrix. Then for all $i, j \in \{1, \dots, p\}$,

$$\operatorname{Cov}\bigl((JX)_i, (JX)_j\bigr) = \sum_{a=1}^{m} \sum_{b=1}^{m} J_{ia} J_{jb} \operatorname{Cov}(X_a, X_b).$$

The right side is the $(i, j)$ entry of $J \operatorname{Cov}(X) J^{\mathsf T}$; cross-covariances are retained.
