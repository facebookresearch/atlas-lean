# The covariance operator on kernel expansions

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. Write $\bar C$ for the [covariance operator](cov-op.md), $K$ for the [Gram matrix](gram.md) and $V_\alpha = \sum_i \alpha_i \Phi(x_i)$ for the [kernel expansion](expansion.md) with coefficients $\alpha \in \mathbb{R}^M$. For every $\alpha \in \mathbb{R}^M$,

$$\bar C V_\alpha = \frac1M\, V_{K\alpha} = \frac1M \sum_i (K\alpha)_i\, \Phi(x_i).$$

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, equation (2.9).
