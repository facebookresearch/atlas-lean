# Kernel expansion in feature space

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. For coefficients $\alpha \in \mathbb{R}^M$, the kernel expansion is the vector

$$V_\alpha = \sum_{i=1}^M \alpha_i\, \Phi(x_i) \in F.$$

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, equation (2.8).
