# Generalized least-squares estimate under the linear model

Let $X$ be a real $n \times p$ matrix and $V$ a real $n \times n$ matrix with $X^\top V^{-1}X$ invertible, and write $\hat\beta(y) = (X^\top V^{-1}X)^{-1}X^\top V^{-1}y$ for the generalized least-squares estimator. Then for every $\beta \in \mathbb{R}^p$ and $e \in \mathbb{R}^n$, $\hat\beta(X\beta + e) = \beta + (X^\top V^{-1}X)^{-1}X^\top V^{-1}e$.
