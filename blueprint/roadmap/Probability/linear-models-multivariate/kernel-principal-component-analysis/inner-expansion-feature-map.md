# Kernel PCA projections

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. For $\alpha \in \mathbb{R}^M$ and a test point $t \in X$, the projection of $\Phi(t)$ onto $V_\alpha = \sum_i \alpha_i \Phi(x_i)$ is

$$\langle V_\alpha, \Phi(t)\rangle = \sum_i \alpha_i\, k(x_i, t),$$

computed from kernel values only.

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, equation (2.15).
