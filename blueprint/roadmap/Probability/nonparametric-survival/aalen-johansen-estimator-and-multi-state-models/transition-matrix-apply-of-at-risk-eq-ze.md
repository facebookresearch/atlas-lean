# Empty risk sets freeze a state

Consider left-truncated multi-state data on increasing grid times: each subject enters at a grid index, is observed until its exit, and has a state path; $Y_h(t_j)$ counts subjects under observation in state $h$ just before $t_j$ and $N_{hl}(t_j)$ those moving from $h$ to $l$ at $t_j$; $\hat P(s, t) = \prod_{s<t_j\le t}(I + \Delta\hat\Lambda(t_j))$ with Nelson–Aalen jumps on these risk sets. If nobody is at risk in $h$ at any grid time in $(s, t]$, row $h$ of $\hat P(s, t)$ is the identity row.
