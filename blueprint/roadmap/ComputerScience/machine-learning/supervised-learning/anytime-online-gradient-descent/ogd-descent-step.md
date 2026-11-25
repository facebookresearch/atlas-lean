# One-round descent inequality for projected gradient steps

Let $E$ be a real inner product space and $\mathrm{proj} : E \to E$ a $1$-Lipschitz (nonexpansive) map that fixes a comparator $x^\star$, i.e. $\mathrm{proj}(x^\star) = x^\star$. Then for all $x, g \in E$ and every step size $\eta > 0$,

$$\langle g,\, x - x^\star\rangle \le \frac{\|x - x^\star\|^2 - \|\mathrm{proj}(x - \eta g) - x^\star\|^2}{2\eta} + \frac{\eta}{2}\,\|g\|^2 .$$
