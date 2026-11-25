# The posterior covariance is positive semidefinite

Let $n$ and $p$ be finite index sets,
let $S$ be a positive semidefinite real $n \times n$ matrix, let $R$ be a positive definite real
$p \times p$ matrix and let $H$ be a real $p \times n$ matrix. Then
$S - S H^\top (H S H^\top + R)^{-1} H S$ is positive semidefinite.

This matrix is the Schur complement of the lower-right block in the joint covariance
$\begin{pmatrix} S & S H^\top \\ H S & H S H^\top + R \end{pmatrix}$ of a linear-Gaussian model.
