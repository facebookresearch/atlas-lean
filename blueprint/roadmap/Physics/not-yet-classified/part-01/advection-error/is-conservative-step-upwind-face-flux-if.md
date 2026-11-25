# Conservative upwind step is the periodic upwind update

Let $n$ cells be indexed periodically by $\mathbb Z/n$, with $\text{area} > 0$, $\Delta x > 0$ and speed $v \ge 0$. A state $c^{\text{next}}$ is reached from $c$ by the conservative shared-face step with time step $\Delta t$ and the upwind face flux if and only if, for every $i$,

$$c^{\text{next}}_i = (1 - \nu)\,c_i + \nu\,c_{i-1}, \qquad \nu = v\,\Delta t/\Delta x.$$
