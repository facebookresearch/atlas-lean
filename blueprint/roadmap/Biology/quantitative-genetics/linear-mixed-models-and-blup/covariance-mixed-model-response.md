# Marginal covariance of the mixed-model response

Let $n$, $p$, $q$ be finite index sets, $P$ a probability measure on $\Omega$, and
$\gamma : \Omega \to \mathbb{R}^q$ (random effects) and $\varepsilon : \Omega \to \mathbb{R}^n$
(residuals) measurable random vectors that are independent under $P$. Let $X$ be a real $n \times p$
matrix, $\beta \in \mathbb{R}^p$, $Z$ a real $n \times q$ matrix and
$Y = X\beta + Z\gamma + \varepsilon$ the response. Let $G$ and $R$ be positive semidefinite
$q \times q$ and $n \times n$ matrices, and suppose $\gamma \sim N(0, G)$ and
$\varepsilon \sim N(0, R)$ under $P$. Then for all indices $i, j$, the covariance of the coordinates
$Y_i$ and $Y_j$ under $P$ is $\operatorname{Cov}(Y_i, Y_j) = (Z G Z^\top + R)_{ij}$, the entry of
the
[phenotypic covariance](../../../Probability/linear-models-multivariate/generalized-least-squares/phen-cov.md).
