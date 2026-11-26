# Summed multi-state risk sets are the delayed-entry risk sets

Consider left-truncated multi-state data on increasing grid times: each subject enters at a grid index, is observed until its exit, and has a state path; $Y_h(t_j)$ counts subjects under observation in state $h$ just before $t_j$ and $N_{hl}(t_j)$ those moving from $h$ to $l$ at $t_j$; $\hat P(s, t) = \prod_{s<t_j\le t}(I + \Delta\hat\Lambda(t_j))$ with Nelson–Aalen jumps on these risk sets. Then $\sum_hY_h(t_j)$ is the delayed-entry number at risk of the data without states.
