# Covariance of the generalized least-squares estimator

Let $X$ be a real $n \times p$ matrix and $V$ a positive definite real $n \times n$ matrix with $X^\top V^{-1}X$ invertible, and write $\hat\beta(y) = (X^\top V^{-1}X)^{-1}X^\top V^{-1}y$ for the generalized least-squares estimator. Let $\varepsilon$ be a random vector in $\mathbb{R}^n$ on a probability space and $\beta \in \mathbb{R}^p$. If the coordinates of $\varepsilon$ are square integrable with $\operatorname{Cov}(\varepsilon_i, \varepsilon_j) = V_{ij}$, then

$$\operatorname{Cov}\big(\hat\beta_a, \hat\beta_b\big) = \big[(X^\top V^{-1}X)^{-1}\big]_{ab}, \qquad \hat\beta = \hat\beta(X\beta + \varepsilon).$$

No mean-zero assumption is needed.
