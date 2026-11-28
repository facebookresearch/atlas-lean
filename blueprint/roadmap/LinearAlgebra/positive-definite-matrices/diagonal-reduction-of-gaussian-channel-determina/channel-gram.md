# Channel matrix HᵀR⁻¹H

For a finite index set $m$, an arbitrary index set $n$ and real matrices $H \in \mathbb{R}^{m \times n}$, $R \in \mathbb{R}^{m \times m}$, the channel matrix is $H^{\top} R^{-1} H \in \mathbb{R}^{n \times n}$, where $R^{-1}$ is the inverse of $R$ when $R$ is invertible and the zero matrix by convention otherwise. The formula is purely algebraic: for $H = [1]$ and $R = [-1]$ it gives $[-1]$, not a Gram matrix. When the noise covariance $R$ is positive definite, it is the Gram matrix of the whitened channel $R^{-1/2} H$.
