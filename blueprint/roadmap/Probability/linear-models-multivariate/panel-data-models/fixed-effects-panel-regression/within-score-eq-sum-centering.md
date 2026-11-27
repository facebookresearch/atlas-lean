# Within score via time-demeaning

For clusters $i = 0, 1, \dots$ let $X_i$ be a real $T \times k$ regressor matrix and $v_i \in \mathbb{R}^T$ a response over a finite set of $T$ periods, and let $Q = I - T^{-1}J$, with $J$ the $T \times T$ all-ones matrix, be the time-demeaning matrix. Then the within score of the first $N$ clusters equals $\sum_{i<N}(QX_i)^\top(Qv_i)$.
