# The kernel Gram matrix is the Gram matrix of the feature vectors

Let $X$ be a set, $F$ a real inner product space, $\Phi : X \to F$ a feature map and $x_1, \dots, x_M \in X$ data points, with kernel $k(x, y) = \langle \Phi(x), \Phi(y)\rangle$. The [kernel Gram matrix](gram.md) $K$ equals the Gram matrix $(\langle v_i, v_j\rangle)_{i,j}$ of the family of vectors $v_i = \Phi(x_i)$ in $F$; in particular it is positive semidefinite.

## Sources

- B. Schölkopf, A. Smola and K.-R. Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), 1299–1319, equation (2.10).
