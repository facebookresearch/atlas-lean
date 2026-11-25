# Anytime step-size schedule gives a square-root regret bound

Let $D > 0$, $G > 0$ and $T \in \mathbb{N}$. Let $a, c : \mathbb{N} \to \mathbb{R}$ satisfy $0 \le a_t \le D^2$ and $c_t \le G^2$ for all $t$, and let the step sizes be $\eta_t = D / (G\sqrt{t+1})$. Then

$$\sum_{t=0}^{T-1} \left( \frac{a_t - a_{t+1}}{2\eta_t} + \frac{\eta_t}{2}\, c_t \right) \le \frac{3}{2}\, G\, D\, \sqrt{T} .$$

With $a_t = \|x_t - x^\star\|^2$ and $c_t = \|g_t(x_t)\|^2$ this turns the per-round descent decomposition of online gradient descent into its anytime regret bound.
