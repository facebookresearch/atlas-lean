# Local compression preserves lookup at positive scales

For all $n, i, j \in \mathbb{N}$ and Boolean region quadtrees $t_0, t_1, t_2, t_3$, the lookup of
the cell $(i, j)$ at scale $n + 1$ in the result of the compressing branch constructor applied to
$t_0, t_1, t_2, t_3$ equals the lookup of $(i, j)$ at scale $n + 1$ in the branch
$Q(t_0, t_1, t_2, t_3)$.

Scale $0$ is excluded: four leaves $L(\mathrm{true})$ collapse to $L(\mathrm{true})$, which gives
true at scale $0$, while a branch gives false there.
