# The within estimator is the truth plus a noise term

For clusters $i$ let $X_i$ be a random real $T \times k$ regressor matrix over a nonempty finite set of $T$ periods, $c_i$ a real individual effect and $u_i \in \mathbb{R}^T$ an error, with responses $y_i = X_i\beta + c_i\mathbf 1 + u_i$; let $Q = I - T^{-1}J$, with $J$ the $T \times T$ all-ones matrix. If the within Gram matrix $G_N = \sum_{i<N}(QX_i)^\top QX_i$ is invertible, then the within estimator of the first $N$ clusters equals $\beta + G_N^{-1}\sum_{i<N}(QX_i)^\top Qu_i$; the individual effects drop out.
