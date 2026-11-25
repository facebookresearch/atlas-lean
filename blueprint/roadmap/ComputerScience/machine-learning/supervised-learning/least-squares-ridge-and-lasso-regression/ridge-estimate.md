# Ridge estimate

For a real matrix $X$ with $m$ rows and columns indexed by a finite set
$\iota$, responses $y \in \mathbb{R}^m$ and a real number $\lambda$, the ridge estimate is
$(X^\top X + \lambda I)^{-1} X^\top y \in \mathbb{R}^\iota$.

The inverse of a singular matrix is taken to be $0$; for $\lambda > 0$ the matrix
$X^\top X + \lambda I$ is always invertible.
