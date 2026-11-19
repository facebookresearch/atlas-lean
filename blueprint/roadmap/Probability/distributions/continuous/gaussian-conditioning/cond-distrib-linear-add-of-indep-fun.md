# Bayes' theorem for a linear-Gaussian observation

Let $n$ and $p$ be finite index sets,
and let $x$ and $v$ be independent measurable random vectors in $\mathbb{R}^n$ and $\mathbb{R}^p$
on a probability space, with $x \sim N(m, S)$ and $v \sim N(0, R)$ for positive semidefinite
matrices $S$ and $R$. Let $H$ be a real $p \times n$ matrix such that $H S H^\top + R$ is
invertible, and let $Y = H x + v$. Then for almost every $y$ with respect to the law of $Y$, the
conditional distribution of $x$ given $Y = y$ is the Gaussian with mean
$m + S H^\top (H S H^\top + R)^{-1} (y - H m)$ and covariance
$S - S H^\top (H S H^\top + R)^{-1} H S$.
