# Conditional mean of the response given the random effects

Let $n$, $p$, $q$ be finite index sets, $P$ a probability measure on $\Omega$, and
$\gamma : \Omega \to \mathbb{R}^q$ (random effects) and $\varepsilon : \Omega \to \mathbb{R}^n$
(residuals) measurable random vectors that are independent under $P$. Let $X$ be a real $n \times p$
matrix, $\beta \in \mathbb{R}^p$, $Z$ a real $n \times q$ matrix and
$Y = X\beta + Z\gamma + \varepsilon$ the response. Let $R$ be a real $n \times n$ matrix and suppose
$\varepsilon \sim N(0, R)$ under $P$; nothing is assumed about the law of $\gamma$. Then for almost
every $g$ with respect to the law of $\gamma$, the conditional distribution of $Y$ given
$\gamma = g$ has mean $X\beta + Zg$. Here $N(m, S)$ is the multivariate Gaussian measure with mean
$m$ and covariance $S$ when $S$ is positive semidefinite; for any other matrix $S$ its definition
gives the point mass at $m$.
