# Gauss–Markov theorem in covariance form

Let $X$ be a real $m \times k$ design matrix with $X^\top X$ invertible, and consider the linear model $y = X\beta + \varepsilon$ with $\beta \in \mathbb{R}^k$ and a random error vector $\varepsilon$ in $\mathbb{R}^m$ on a probability space whose coordinates are integrable with mean zero and square integrable with $\operatorname{Cov}(\varepsilon_i, \varepsilon_j) = \sigma^2 \mathbf 1[i = j]$. Write $\hat\beta(y) = (X^\top X)^{-1} X^\top y$ for the ordinary least-squares estimator. Let $A$ be a real $k \times m$ matrix such that $\mathbb{E}[A(X\beta' + \varepsilon)] = \beta'$ for every $\beta' \in \mathbb{R}^k$ (a linear unbiased estimator). Then for every $\beta$ the difference of covariance matrices

$$\operatorname{Cov}\big(A y\big) - \operatorname{Cov}\big(\hat\beta(y)\big), \qquad y = X\beta + \varepsilon,$$

is positive semidefinite: ordinary least squares is the best linear unbiased estimator.

## Sources

- C. F. Gauss, *Theoria combinationis observationum erroribus minimis obnoxiae* (1823); A. C. Aitken, "On Least Squares and Linear Combination of Observations", *Proceedings of the Royal Society of Edinburgh* 55 (1936), 42–48.
