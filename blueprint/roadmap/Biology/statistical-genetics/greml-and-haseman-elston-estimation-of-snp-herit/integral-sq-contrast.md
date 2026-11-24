# Second moments of the rotated contrasts under the GREML model

Let $m$, $k$ and $r$ be finite index sets, $X$ a real $m \times k$ matrix, $K$ a real $m \times m$
matrix, $B$ a real $r \times m$ matrix and $d \in \mathbb{R}^r$ with $BX = 0$, $BB^\top = I$,
$|r| + |k| = |m|$ and $BKB^\top = \operatorname{diag}(d)$
([diagonalizing orthonormal error contrast](is-spectral-contrast.md)). Let
$\theta_0 = (\sigma_{g,0}^2, \sigma_{e,0}^2)$ be such that
$V(\theta_0) = \sigma_{g,0}^2 K + \sigma_{e,0}^2 I$ is positive semidefinite, let
$\beta \in \mathbb{R}^k$, and let $y$ be a random vector in $\mathbb{R}^m$ on a measure space
$(\Omega, \mu)$ whose law under $\mu$ is the Gaussian $N(X\beta, V(\theta_0))$; in particular
$\mu$ is a probability measure. Then for every $i \in r$ the rotated contrast $w_i = (By)_i$ is
square integrable and

$$\mathbb{E}[w_i^2] = \sigma_{g,0}^2 d_i + \sigma_{e,0}^2.$$
