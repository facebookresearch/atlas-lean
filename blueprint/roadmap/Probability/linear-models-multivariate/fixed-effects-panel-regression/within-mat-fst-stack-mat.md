# Demeaning the stacked regressors by cluster

For clusters $i = 0, 1, \dots$ let $X_i$ be a real $T \times k$ regressor matrix and $v_i \in \mathbb{R}^T$ a response over a finite set of $T$ periods, and let $Q = I - T^{-1}J$, with $J$ the $T \times T$ all-ones matrix, be the time-demeaning matrix. Then demeaning the stacked regressor matrix of the first $N$ clusters within clusters gives the row $(QX_i)_t$ at $(i, t)$.
