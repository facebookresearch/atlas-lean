# The left-truncated Aalen–Johansen estimator is a stochastic matrix

Consider left-truncated multi-state data on increasing grid times: each subject enters at a grid index, is observed until its exit, and has a state path; $Y_h(t_j)$ counts subjects under observation in state $h$ just before $t_j$ and $N_{hl}(t_j)$ those moving from $h$ to $l$ at $t_j$; $\hat P(s, t) = \prod_{s<t_j\le t}(I + \Delta\hat\Lambda(t_j))$ with Nelson–Aalen jumps on these risk sets. Every entry of $\hat P(s, t)$ is nonnegative.
