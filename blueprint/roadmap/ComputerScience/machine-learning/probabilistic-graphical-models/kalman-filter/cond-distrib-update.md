# The update step is the exact posterior

Let $x$ be a measurable random vector in
$\mathbb{R}^n$ and $v$ a measurable random vector in $\mathbb{R}^p$ on a probability space, with
$x$ independent of $v$. Suppose $x$ has the law $N(m, P)$ of a belief with mean $m$ and positive
semidefinite covariance $P$, and $v$ has law $N(0, R)$ with $R$ positive semidefinite. Let $H$ be
a real $p \times n$ matrix with $H P H^\top + R$ invertible, and put $Y = H x + v$. Then for
almost every $y$ with respect to the law of $Y$, the conditional distribution of $x$ given
$Y = y$ is the law of the belief obtained from $(m, P)$ by the update with $H$, $R$ and the
observation $y$.
