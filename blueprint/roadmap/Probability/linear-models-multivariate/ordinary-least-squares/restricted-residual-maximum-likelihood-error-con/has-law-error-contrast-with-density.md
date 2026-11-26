# Density of an error contrast

Let $X$ be a real $n \times p$ design matrix, $A$ an error contrast for $X$ ($A X = 0$, $A A^\top$ invertible, $r = n - p$ rows), $V$ a real positive definite $n \times n$ matrix and $\beta \in \mathbb{R}^p$. If the random vector $y$ has the Gaussian law $N(X\beta, V)$, then $A y$ has density

$$\varphi_{A V A^\top}(z) = (2\pi)^{-r/2} \det(A V A^\top)^{-1/2} \exp\!\big(-\tfrac12 z^\top (A V A^\top)^{-1} z\big)$$

with respect to Lebesgue measure on $\mathbb{R}^r$.
