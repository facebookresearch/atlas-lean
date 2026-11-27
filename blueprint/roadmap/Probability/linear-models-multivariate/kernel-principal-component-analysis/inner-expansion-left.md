# Inner products of a kernel expansion

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. For $\alpha \in \mathbb{R}^M$ and $W \in F$,

$$\Big\langle \sum_i \alpha_i \Phi(x_i),\ W\Big\rangle = \sum_i \alpha_i\, \langle \Phi(x_i), W\rangle.$$

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, equations (2.9) and (2.14).
