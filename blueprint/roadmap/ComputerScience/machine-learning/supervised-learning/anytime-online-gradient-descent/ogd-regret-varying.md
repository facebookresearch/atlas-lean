# Regret decomposition for varying-step online gradient descent

Let $E$ be a real inner product space, $f : \mathbb{N} \to E \to \mathbb{R}$ the per-round costs, $g : \mathbb{N} \to E \to E$ and $\eta : \mathbb{N} \to \mathbb{R}$ with $\eta_t > 0$ for all $t$. Let $\mathrm{proj} : E \to E$ be $1$-Lipschitz with $\mathrm{proj}(x^\star) = x^\star$ for a comparator $x^\star \in E$, and assume the subgradient inequality toward $x^\star$:

$$f_t(x) + \langle g_t(x),\, x^\star - x\rangle \le f_t(x^\star) \quad \text{for all } t \in \mathbb{N},\ x \in E .$$

Let $x_t$ be the projected online gradient descent iterates from $x_0$ with steps $\eta_t$. Then for every $T \in \mathbb{N}$,

$$\sum_{t=0}^{T-1} \big(f_t(x_t) - f_t(x^\star)\big) \le \sum_{t=0}^{T-1} \left( \frac{\|x_t - x^\star\|^2 - \|x_{t+1} - x^\star\|^2}{2\eta_t} + \frac{\eta_t}{2}\, \|g_t(x_t)\|^2 \right).$$
