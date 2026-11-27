# The centred Gram matrix

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. Let $K$ be the [kernel Gram matrix](gram.md) and $1_M$ the $M \times M$ matrix with all entries $1/M$. Then the Gram matrix $\tilde K_{ij} = \langle \tilde\Phi(x_i), \tilde\Phi(x_j)\rangle$ of the [centred feature vectors](centred-feature.md) is

$$\tilde K = K - 1_M K - K 1_M + 1_M K 1_M,$$

computed from the kernel values alone.

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, Appendix B, equation (B.3).
