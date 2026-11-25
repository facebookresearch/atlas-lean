# Proximal contamination

Let $I$ be a finite index set, let $V_0$ be a positive definite real $I \times I$ matrix, let $c \ge 0$ and let $x, y \in \mathbb{R}^I$. Then the [mixed-model statistic](mm-chi-sq.md) satisfies

$$\chi^2(V_0 + c\, x x^\top) = \frac{\chi^2(V_0)}{1 + c\, x^\top V_0^{-1} x}.$$

Including the candidate marker $x$ in the covariance (through a genetic relationship matrix built from markers that include $x$) deflates the statistic by this exact factor, for every phenotype $y$.
