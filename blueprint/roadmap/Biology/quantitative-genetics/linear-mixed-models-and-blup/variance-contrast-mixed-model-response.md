# Variance of a linear combination of the response

Let $n$, $p$, $q$ be finite index sets, $P$ a probability measure on $\Omega$, and
$\gamma : \Omega \to \mathbb{R}^q$ (random effects) and $\varepsilon : \Omega \to \mathbb{R}^n$
(residuals) measurable random vectors that are independent under $P$. Let $X$ be a real $n \times p$
matrix, $\beta \in \mathbb{R}^p$, $Z$ a real $n \times q$ matrix and
$Y = X\beta + Z\gamma + \varepsilon$ the response. Let $G$ and $R$ be positive semidefinite
$q \times q$ and $n \times n$ matrices, and suppose $\gamma \sim N(0, G)$ and
$\varepsilon \sim N(0, R)$ under $P$. Then for every coefficient vector $c \in \mathbb{R}^n$, the
linear combination $\sum_k c_k Y_k$ has variance $c^\top (Z G Z^\top + R)\, c$ under $P$, the
quadratic form of the
[phenotypic covariance](../../../Probability/linear-models-multivariate/generalized-least-squares/phen-cov.md).
The coefficients need not sum to zero.
