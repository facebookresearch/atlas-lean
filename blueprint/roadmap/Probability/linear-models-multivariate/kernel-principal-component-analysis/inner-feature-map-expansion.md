# Feature vectors against a kernel expansion

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. For $\alpha \in \mathbb{R}^M$ and every index $k$,

$$\Big\langle \Phi(x_k),\ \sum_i \alpha_i \Phi(x_i)\Big\rangle = (K\alpha)_k,$$

where $K$ is the [kernel Gram matrix](gram.md).

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, equations (2.9)–(2.10).
