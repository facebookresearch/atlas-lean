# The kernel PCA Gram matrix is positive semidefinite

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. The [kernel Gram matrix](gram.md) $K = (\langle \Phi(x_i), \Phi(x_j)\rangle)_{i,j}$ is positive semidefinite, as a Gram matrix of feature vectors; equivalently, the eigenvalues $M\lambda$ of $K$ in the Gram-matrix eigenproblem are nonnegative.

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, equations (2.10) and (2.12).
