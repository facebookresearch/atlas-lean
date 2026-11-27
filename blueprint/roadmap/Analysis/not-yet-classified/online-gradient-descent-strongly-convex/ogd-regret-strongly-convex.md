# Regret of online gradient descent for strongly convex losses

Let $E$ be a real inner product space, $\alpha > 0$, $G \ge 0$ and $T \ge 1$. Let the projection $\Pi$ be 1-Lipschitz and fix the comparator, $\Pi(x^*) = x^*$. Suppose the iterates satisfy

$$x_{t+1} = \Pi\!\left(x_t - \frac{1}{\alpha (t + 1)}\,g_t(x_t)\right),$$

the losses satisfy the strong-convexity inequality at the comparator, $f_t(x_t) + \langle g_t(x_t), x^* - x_t\rangle + \frac{\alpha}{2}\lVert x^* - x_t\rVert^2 \le f_t(x^*)$, and $\lVert g_t(x_t)\rVert \le G$ for all $t$. Then

$$\sum_{t=0}^{T-1} \bigl(f_t(x_t) - f_t(x^*)\bigr) \le \frac{G^2}{2\alpha}\,(1 + \log T).$$
