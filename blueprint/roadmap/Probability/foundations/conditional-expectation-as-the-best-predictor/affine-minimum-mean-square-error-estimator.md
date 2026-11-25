# Affine minimum mean-square-error estimator

Let $X$ and $Y$ be random vectors in $\mathbb{R}^n$ and $\mathbb{R}^p$ on one probability space, each with finite second moments. Write $m_X = \mathbb{E}[X]$, $m_Y = \mathbb{E}[Y]$, $\Sigma_{XX} = \operatorname{Cov}(X)$, $\Sigma_{XY} = \operatorname{Cov}(X, Y) = \Sigma_{YX}^\top$ and $\Sigma_{YY} = \operatorname{Cov}(Y)$, and assume that $\Sigma_{YY}$ is positive definite. Set

$$K = \Sigma_{XY} \Sigma_{YY}^{-1}, \qquad \hat X = m_X + K (Y - m_Y).$$

1. **Minimality.** For every matrix $A \in \mathbb{R}^{n \times p}$ and vector $b \in \mathbb{R}^n$,

    $$\mathbb{E}\|X - AY - b\|^2 = \mathbb{E}\|X - \hat X\|^2 + \operatorname{tr}\big((A - K)\Sigma_{YY}(A - K)^\top\big) + \|m_X - A m_Y - b\|^2 .$$

    Hence $\hat X$ minimizes the mean squared error among all affine functions $AY + b$ of $Y$, the pair $(A, b) = (K, m_X - K m_Y)$ is the only minimizer, and the minimum is $\operatorname{tr}(\Sigma_{XX} - \Sigma_{XY}\Sigma_{YY}^{-1}\Sigma_{YX})$. The same pair also minimizes the error second-moment matrix $\mathbb{E}[(X - AY - b)(X - AY - b)^\top]$ in the positive semidefinite order.

2. **Unbiased and uncorrelated error.** $\mathbb{E}[X - \hat X] = 0$ and $\operatorname{Cov}(X - \hat X, Y) = 0$.
3. **Gaussian case.** If $(X, Y)$ is jointly Gaussian, then $\hat X = \mathbb{E}[X \mid Y]$ almost surely, so the affine estimator is the minimum mean-square-error estimator among all square-integrable functions of $Y$.
4. **A non-Gaussian pair where they differ.** Let $Y$ be a standard normal real random variable and $X = Y^2$. Then $\hat X = 1$, while $\mathbb{E}[X \mid Y] = Y^2$ almost surely, and $\mathbb{E}(X - \hat X)^2 = 2 > 0 = \mathbb{E}(X - \mathbb{E}[X \mid Y])^2$.

**Proof.** For a random vector $Z$ with finite second moments, $\mathbb{E}\|Z\|^2 = \operatorname{tr}\operatorname{Cov}(Z) + \|\mathbb{E}Z\|^2$. For $Z = X - AY - b$, bilinearity of covariance gives $\mathbb{E}Z = m_X - A m_Y - b$ and

$$\operatorname{Cov}(Z) = \Sigma_{XX} - A\Sigma_{YX} - \Sigma_{XY}A^\top + A\Sigma_{YY}A^\top = (A - K)\Sigma_{YY}(A - K)^\top + \Sigma_{XX} - \Sigma_{XY}\Sigma_{YY}^{-1}\Sigma_{YX},$$

where the second equality expands the right side using $K\Sigma_{YY} = \Sigma_{XY}$ and the symmetry of $\Sigma_{YY}$. At $(A, b) = (K, m_X - K m_Y)$ the first and last terms vanish, which identifies $\mathbb{E}\|X - \hat X\|^2$ with $\operatorname{tr}(\Sigma_{XX} - \Sigma_{XY}\Sigma_{YY}^{-1}\Sigma_{YX})$ and proves the displayed identity. All three terms are nonnegative. Since $\Sigma_{YY}$ is positive definite, $\operatorname{tr}((A - K)\Sigma_{YY}(A - K)^\top) = 0$ only when $A = K$, and then the last term vanishes only when $b = m_X - K m_Y$; this is uniqueness. Without traces, $\mathbb{E}[ZZ^\top] = \operatorname{Cov}(Z) + \mathbb{E}Z\,\mathbb{E}Z^\top$ is the error second-moment matrix of $\hat X$ plus two positive semidefinite matrices, which gives the matrix form of part 1. For part 2, $\mathbb{E}[X - \hat X] = m_X - m_X = 0$ and $\operatorname{Cov}(X - \hat X, Y) = \Sigma_{XY} - K\Sigma_{YY} = 0$.

For part 3, by Gaussian conditioning the conditional law of $X$ given $Y = y$ is, for almost every $y$ with respect to the law of $Y$, Gaussian with mean $m_X + \Sigma_{XY}\Sigma_{YY}^{-1}(y - m_Y)$; the conditional expectation is the mean of the conditional law, so $\mathbb{E}[X \mid Y] = \hat X$ almost surely, and it is the minimum mean-square-error predictor among square-integrable functions of $Y$. For part 4, $X$ has finite second moments, $\operatorname{Cov}(X, Y) = \mathbb{E}[Y^3] - \mathbb{E}[Y^2]\,\mathbb{E}[Y] = 0$ and $\mathbb{E}X = 1$, so $K = 0$ and $\hat X = 1$. Since $X$ is a measurable function of $Y$, $\mathbb{E}[X \mid Y] = X$ almost surely, and $\mathbb{E}(Y^2 - 1)^2 = \mathbb{E}Y^4 - 2\,\mathbb{E}Y^2 + 1 = 3 - 2 + 1 = 2$.

## Proof depends on

- [Gaussian conditioning (Schur complement)](../../distributions/continuous/gaussian-conditioning/cond-distrib-multivariate-gaussian.md): the conditional law of one block of a Gaussian vector given the other, used for part 3

## Background

- [The conditional mean minimizes the expected squared error](integral-sq-sub-cond-exp-le.md): the minimality of the conditional expectation among all square-integrable predictors, which part 3 identifies with the affine estimator in the Gaussian case

## Sources

- B. D. O. Anderson and J. B. Moore, *Optimal Filtering*, Prentice-Hall, 1979, <https://users.cecs.anu.edu.au/~john/papers/BOOK/B02.PDF>, Section 5.2: the linear minimum variance estimator $m_x + \Sigma_{xy}\Sigma_{yy}^{-1}(y - m_y)$ (Theorem 2.1, (2.2), p. 93, with the trace decomposition in its proof), its minimization of the error covariance matrix (remark after the proof, pp. 93–94), its agreement with the minimum variance estimator for jointly Gaussian variables (Theorem 2.2, p. 94) and its unbiasedness (Theorem 2.3, p. 94). Uniqueness, the uncorrelated error and the non-Gaussian example are derived on the page.
