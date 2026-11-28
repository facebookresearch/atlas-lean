# Mean and covariance of an error contrast

Let $X$ be a real $n \times p$ design matrix, $A$ a real $r \times n$ matrix with $A X = 0$, $V$ a real positive semidefinite $n \times n$ matrix and $\beta \in \mathbb{R}^p$. If the random vector $y$ has the Gaussian law $N(X\beta, V)$, then $\mathbb{E}[A y] = 0$ and, for all $i, j$,

$$\operatorname{Cov}\big((A y)_i, (A y)_j\big) = (A V A^\top)_{ij}.$$
