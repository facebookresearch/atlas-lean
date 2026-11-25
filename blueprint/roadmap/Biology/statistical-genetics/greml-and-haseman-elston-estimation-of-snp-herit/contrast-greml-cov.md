# Diagonalizing contrasts make the GREML contrast covariance diagonal

Let $K$ be a real square matrix indexed by a finite set and $B$ a real matrix whose columns are
indexed by the same set, with orthonormal rows, $BB^\top = I$, and with
$BKB^\top = \operatorname{diag}(d)$. Then for every
$\theta = (\sigma_g^2, \sigma_e^2) \in \mathbb{R}^2$ the [GREML covariance](greml-cov.md)
$V(\theta) = \sigma_g^2 K + \sigma_e^2 I$ satisfies

$$B V(\theta) B^\top = \operatorname{diag}\bigl(\sigma_g^2 d_i + \sigma_e^2\bigr)_i.$$

No sign condition on $\sigma_g^2$ or $\sigma_e^2$ is needed.
