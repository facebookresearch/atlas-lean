# REML projection matrix $P = B^\top (B V B^\top)^{-1} B$

For finite index sets $r$ and $m$, a real $r \times m$ matrix $B$ (an error contrast) and a real
$m \times m$ matrix $V$ (a covariance), the REML projection matrix is

$$P = B^\top (B V B^\top)^{-1} B.$$

The matrix inverse is total: $(B V B^\top)^{-1}$ is the inverse of $B V B^\top$ when
$\det(B V B^\top) \ne 0$ and the zero matrix otherwise, so $P = 0$ when $B V B^\top$ is singular.
The intended use has $B V B^\top$ invertible, for example $V$ positive definite and $B$ of full row
rank.
