# Mean squared error as variance plus squared bias for finite weights

Let $p$ be real weights on a finite set with $\sum_x p(x) = 1$, and write $\mathbb{E}_p[X] = \sum_x p(x)X(x)$ and $\operatorname{Var}_p(X) = \mathbb{E}_p[(X - \mathbb{E}_pX)^2]$. Then for every $X$ and $\theta$, $\mathbb{E}_p[(X - \theta)^2] = \operatorname{Var}_p(X) + (\mathbb{E}_pX - \theta)^2$. Nonnegativity of $p$ is not needed.
