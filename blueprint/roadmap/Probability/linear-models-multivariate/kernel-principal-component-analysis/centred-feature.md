# Centred feature vectors

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. The centred feature vectors are

$$\tilde\Phi(x_i) = \Phi(x_i) - \frac1M \sum_{m=1}^M \Phi(x_m), \qquad i = 1, \dots, M.$$

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, Appendix B, equation (B.1).
