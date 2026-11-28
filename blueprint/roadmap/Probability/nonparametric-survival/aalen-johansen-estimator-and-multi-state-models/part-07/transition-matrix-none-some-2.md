# Aalen–Johansen entries are cumulative incidences

For grouped competing-risks data viewed as multi-state data with a transient state and one absorbing state per cause, let $\hat P$ be the Aalen–Johansen transition matrix and $s$ precede every observation time. Then the entry of $\hat P(s, t)$ from the transient state to cause $c$ is $\hat F_c(t) = \sum_{t_j\le t}\hat S(t_j-)d_{j,c}/Y_j$, with $x/0 = 0$ when $Y_j = 0$.
