# Regret of online gradient descent with decreasing steps for strongly convex losses

Let $E$ be a real inner product space, $\mathrm{proj} : E \to E$ $1$-Lipschitz, $f_t : E \to \mathbb{R}$ and $g_t : E \to E$ for $t \in \mathbb{N}$, $\alpha > 0$, $G \ge 0$, $x_0, x^* \in E$ with $\mathrm{proj}(x^*) = x^*$, and $T \ge 1$. Let $x_t$ be the projected online gradient descent iterates with step sizes $\eta_t = 1/(\alpha (t+1))$: $x_{t+1} = \mathrm{proj}(x_t - \eta_t\, g_t(x_t))$. Suppose that for every $t$,

$$f_t(x_t) + \langle g_t(x_t), x^* - x_t \rangle + \frac{\alpha}{2}\, \|x^* - x_t\|^2 \le f_t(x^*) \quad\text{and}\quad \|g_t(x_t)\| \le G.$$

Then

$$\sum_{t=0}^{T-1} \big(f_t(x_t) - f_t(x^*)\big) \le \frac{G^2}{2\alpha}\, (1 + \log T).$$
