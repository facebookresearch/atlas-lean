# Eigenvectors with nonzero eigenvalue lie in the span of the data

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. Let $\bar C$ be the [covariance operator](cov-op.md). If $V \in F$ and $\lambda \ne 0$ satisfy $\bar C V = \lambda V$, then $V$ lies in the span of $\Phi(x_1), \dots, \Phi(x_M)$.

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, Section 2, before equation (2.8).
