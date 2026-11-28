# Projected online gradient descent with varying step sizes

Let $E$ be a real inner product space, $\mathrm{proj} : E \to E$ a map, $g : \mathbb{N} \to E \to E$ the per-round (sub)gradient oracle ($g_t(x)$ is the subgradient of the round-$t$ cost at $x$), $\eta : \mathbb{N} \to \mathbb{R}$ a step-size schedule and $x_0 \in E$ a starting point. The iterates are defined by recursion on the round $t$, counted from $0$:

$$x_0 = x_0, \qquad x_{t+1} = \mathrm{proj}\big(x_t - \eta_t\, g_t(x_t)\big).$$

No positivity of the step sizes and no property of $\mathrm{proj}$ is assumed in the definition.
