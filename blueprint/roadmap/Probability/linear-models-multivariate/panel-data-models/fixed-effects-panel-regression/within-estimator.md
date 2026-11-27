# Within (fixed-effects) estimator of a panel

For clusters $i$ with real $T \times k$ regressor matrices $X_i$, responses $y_i \in \mathbb{R}^T$ and $N \in \mathbb{N}$, the within estimator is

$$\hat\beta_N = \Big(\sum_{i<N}\ddot X_i^\top\ddot X_i\Big)^{-1}\sum_{i<N}\ddot X_i^\top\ddot y_i,$$

where $\ddot{\ }$ denotes demeaning over the cluster's periods and the inverse is the matrix inverse, taken to be $0$ for a singular matrix.

## Sources

- J. M. Wooldridge, *Econometric Analysis of Cross Section and Panel Data*, 2nd ed., MIT Press (2010), Chapter 10.
