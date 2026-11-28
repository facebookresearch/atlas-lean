# Projected online gradient descent

For a real inner product space $E$, a map $P : E \to E$, maps $g_t : E \to E$ for each round $t$, a step size $\eta \in \mathbb{R}$ and a starting point $x_0 \in E$, the iterates are defined by

$$x_{t+1} = P\big(x_t - \eta\, g_t(x_t)\big).$$

The recurrence is defined for arbitrary update data. In projected online gradient descent, $P$ is the projection onto the feasible set, $g_t(x)$ is a subgradient of the round-$t$ cost at $x$, and $\eta > 0$.
