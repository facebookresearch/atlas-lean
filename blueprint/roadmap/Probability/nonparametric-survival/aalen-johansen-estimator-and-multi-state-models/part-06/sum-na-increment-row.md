# Rows of a Nelson–Aalen jump sum to zero

For grouped multi-state data with distinct increasing observation times $t_j$, transition counts $N_{hl}(t_j)$ and numbers at risk $Y_h(t_j)$, let $\Delta\hat\Lambda(t_j)$ be the Nelson–Aalen jump ($N_{hl}/Y_h$ off the diagonal, minus the row sum on it, with $x/0 = 0$ when $Y_h = 0$) and $\hat P(s, t) = \prod_{s<t_j\le t}(I + \Delta\hat\Lambda(t_j))$ the Aalen–Johansen estimator. Every row of $\Delta\hat\Lambda(t_j)$ sums to $0$.
