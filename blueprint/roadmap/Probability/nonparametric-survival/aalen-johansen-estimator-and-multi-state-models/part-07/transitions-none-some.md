# Transient-to-cause transitions are cause-specific failures

Consider left-truncated competing-risks data on increasing grid times with observed causes, viewed as delayed-entry multi-state data with one transient and one absorbing state per cause; let $\hat P$ be its left-truncated Aalen–Johansen estimator, $\hat S(s, t) = \prod_{s<t_j\le t}(1 - d_j/Y_j)$ and $\hat F_c(s, t) = \sum_{s<t_j\le t}\hat S(s, t_j-)d_{j,c}/Y_j$ (factors and terms with $Y_j = 0$ omitted). Then the transitions from the transient state to cause $c$ at $t_j$ are the observed failures $d_{j,c}$.
