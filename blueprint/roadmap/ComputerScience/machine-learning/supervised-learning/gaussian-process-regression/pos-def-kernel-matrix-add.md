# Regularized kernel matrices are positive definite

Let $k$ be a kernel and $x = (x_j)_{j \in \nu}$ a family of training inputs whose kernel matrix $K = K(x, x)$ is positive semidefinite, and let $\sigma^2 > 0$. Then $K + \sigma^2 I$ is positive definite (Rasmussen and Williams 2006, Section 2.2). In particular the marginal law $N(0, K + \sigma^2 I)$ of the targets has a density and its log determinant is finite.
