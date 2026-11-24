# Covariance operator in feature space

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. The covariance operator in feature space is the map $\bar C : F \to F$,

$$\bar C V = \frac1M \sum_{j=1}^M \langle \Phi(x_j), V\rangle\, \Phi(x_j),$$

with $\bar C = 0$ when $M = 0$.

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, equation (2.5).
