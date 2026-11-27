# Fitted values are the hat matrix applied to the response

Let $X$ be a real $n \times p$ design matrix and $y \in \mathbb{R}^n$. The fitted values $X\hat\beta$ of the least-squares estimator $\hat\beta = (X^\top X)^{-1} X^\top y$ equal $H y$, where $H = X (X^\top X)^{-1} X^\top$ is the hat matrix (with the inverse of a singular matrix taken to be zero).
