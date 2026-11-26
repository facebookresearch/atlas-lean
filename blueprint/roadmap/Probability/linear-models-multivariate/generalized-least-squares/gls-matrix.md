# Generalized least-squares matrix

Let $m, k$ be finite index sets, $X$ a real $m \times k$ design matrix and $V$ a real $m \times m$ matrix. The generalized least-squares matrix is

$$B = (X^\top V^{-1} X)^{-1} X^\top V^{-1},$$

where the inverse of a singular matrix is taken to be $0$. When $V$ is positive definite and $X^\top V^{-1} X$ is invertible, $By$ is the GLS estimate of $b$ in the model $y = Xb + e$ with $\operatorname{Cov}(e) = V$.

## Sources

- A. C. Aitken, *On least squares and linear combination of observations*, Proc. Roy. Soc. Edinburgh 55 (1936), 42–48.
