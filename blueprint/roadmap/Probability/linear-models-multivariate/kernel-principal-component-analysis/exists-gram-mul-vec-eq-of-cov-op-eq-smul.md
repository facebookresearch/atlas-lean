# Every kernel principal axis comes from the Gram-matrix eigenproblem

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. Write $\bar C$ for the [covariance operator](cov-op.md), $K$ for the [Gram matrix](gram.md) and $V_\alpha = \sum_i \alpha_i \Phi(x_i)$ for the [kernel expansion](expansion.md) with coefficients $\alpha \in \mathbb{R}^M$. If $V \in F$ and $\lambda \ne 0$ satisfy $\bar C V = \lambda V$, then there is $\alpha \in \mathbb{R}^M$ with $V = V_\alpha$ and $M\lambda\, \alpha = K\alpha$.

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, Appendix A.
