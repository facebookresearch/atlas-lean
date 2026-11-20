# Trees of a run of splays

Over a linear order, for a sequence of keys $x_0, x_1, \dots$ and a binary tree $t$, the trees
$t_0, t_1, \dots$ of the run of splays are defined by $t_0 = t$ and $t_{i+1} = S_{x_i}(t_i)$, the
result of splaying $t_i$ at $x_i$. So $t_i$ is obtained from $t$ by splaying successively at
$x_0, \dots, x_{i-1}$.
