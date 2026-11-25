# Normalization of kernel principal axes

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. Write $\bar C$ for the [covariance operator](cov-op.md), $K$ for the [Gram matrix](gram.md) and $V_\alpha = \sum_i \alpha_i \Phi(x_i)$ for the [kernel expansion](expansion.md) with coefficients $\alpha \in \mathbb{R}^M$. If $M\lambda\, \alpha = K\alpha$, then

$$\|V_\alpha\|^2 = M\lambda\, (\alpha \cdot \alpha);$$

so $V_\alpha$ has unit norm exactly when $M\lambda\, (\alpha \cdot \alpha) = 1$.

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, equation (2.14).
