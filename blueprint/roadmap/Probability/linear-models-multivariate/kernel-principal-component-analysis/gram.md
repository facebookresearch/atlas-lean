# Kernel Gram matrix

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. The kernel Gram matrix is the $M \times M$ matrix

$$K_{ij} = \langle \Phi(x_i), \Phi(x_j)\rangle = k(x_i, x_j).$$

It is the [Gram matrix of the feature vectors](gram-eq-matrix-gram.md).

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, equation (2.10).
