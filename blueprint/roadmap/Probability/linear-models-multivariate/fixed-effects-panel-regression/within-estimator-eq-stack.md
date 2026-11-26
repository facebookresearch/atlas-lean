# Within estimator of the stacked panel

For clusters $i = 0, 1, \dots$ let $X_i$ be a real $T \times k$ regressor matrix and $y_i \in \mathbb{R}^T$ a response over a finite set of $T$ periods. Let $\ddot X$ and $\ddot y$ be the stacked regressor matrix and response of the first $N$ clusters, demeaned within clusters. Then the within estimator of the first $N$ clusters equals $(\ddot X^\top\ddot X)^{-1}\ddot X^\top\ddot y$, where the inverse is the matrix inverse, taken to be $0$ for a singular matrix.
