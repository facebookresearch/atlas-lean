# Conditional covariance of the response given the random effects

Let $n$, $p$, $q$ be finite index sets, $P$ a probability measure on $\Omega$, and
$\gamma : \Omega \to \mathbb{R}^q$ (random effects) and $\varepsilon : \Omega \to \mathbb{R}^n$
(residuals) measurable random vectors that are independent under $P$. Let $X$ be a real $n \times p$
matrix, $\beta \in \mathbb{R}^p$, $Z$ a real $n \times q$ matrix and
$Y = X\beta + Z\gamma + \varepsilon$ the response. Let $R$ be a positive semidefinite $n \times n$
matrix and suppose $\varepsilon \sim N(0, R)$ under $P$; nothing is assumed about the law of
$\gamma$. Then for all indices $i, j$ and almost every $g$ with respect to the law of $\gamma$, the
coordinates $y_i$ and $y_j$ have covariance $R_{ij}$ under the conditional distribution of $Y$ given
$\gamma = g$.
