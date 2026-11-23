# Squared norm of a kernel expansion

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. For every $\alpha \in \mathbb{R}^M$,

$$\Big\|\sum_i \alpha_i \Phi(x_i)\Big\|^2 = \alpha^\top K \alpha,$$

where $K$ is the [kernel Gram matrix](gram.md).

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, equation (2.14), first equality.
