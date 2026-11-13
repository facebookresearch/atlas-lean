# One filter step is the exact posterior

Let $x$ and $w$ be measurable random vectors in
$\mathbb{R}^n$ and $v$ a measurable random vector in $\mathbb{R}^p$ on a probability space, with
$x$ independent of $w$ and the pair $(x, w)$ independent of $v$. Suppose $x$ has the law
$N(m, P)$ of a belief with mean $m$ and positive semidefinite covariance $P$, $w$ has law
$N(0, Q)$ and $v$ has law $N(0, R)$, with $Q$ and $R$ positive semidefinite. Let $F$ be a real
$n \times n$ matrix and $H$ a real $p \times n$ matrix with $H (F P F^\top + Q) H^\top + R$
invertible, and put $x' = F x + w$ and $Y = H x' + v$. Then for almost every $y$ with respect to
the law of $Y$, the conditional distribution of $x'$ given $Y = y$ is the law of the belief
obtained from $(m, P)$ by one filter step with $F$, $Q$, $H$, $R$ and the observation $y$.
