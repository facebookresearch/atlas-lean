# The SIR densities satisfy the integral equation of the drift

For all real $\beta$ and $\gamma$, let $(s, i, r)$ be a
[solution of the SIR system](../kermack-mckendrick-sir-model/is-solution.md) with transmission rate
$\beta$, removal rate $\gamma$ and population size $1$ (in densities), and $x(t) = (s(t), i(t))$.
Then for every $t \ge 0$

$$x(t) = x(0) + \int_0^t F(x(u))\, du,$$

with the [drift](drift.md) $F$.
