# LSDV slope equals the within estimator

Stack the first $N$ clusters of a panel, with regressor matrices $X_i$ and responses $y_i$ over a finite set of periods, into $X$ and $y$, and let $D$ be the matrix of cluster dummies. Suppose $(\alpha, \beta)$ satisfies the least-squares normal equations $D^\top(y - D\alpha - X\beta) = 0$ and $X^\top(y - D\alpha - X\beta) = 0$, and the within Gram matrix $G = \sum_i \ddot X_i^\top \ddot X_i$ is invertible, where $\ddot X_i$ and $\ddot y_i$ are demeaned over periods. Then $\beta = G^{-1} \sum_i \ddot X_i^\top \ddot y_i$, the within estimator.
