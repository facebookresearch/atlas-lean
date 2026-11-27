# Multiplying the Dirichlet density by a multinomial likelihood

Let
$\alpha = (\alpha_0, \dots, \alpha_n) \in \mathbb{R}^{n+1}$ and let $k = (k_0, \dots, k_n)$ be
natural numbers; write $D_\beta$ for the unnormalized Dirichlet density with parameters $\beta$.
For every $x \in \mathbb{R}^n$, let $\theta = (x_0, \dots, x_{n-1}, 1 - \sum_{i=0}^{n-1} x_i)$ be
its completion to a vector summing to $1$, and write $\theta_i^+ = \max(\theta_i, 0)$. Then

$$D_\alpha(x) \prod_{i=0}^{n} (\theta_i^+)^{k_i} = D_{\alpha + k}(x).$$

Both sides vanish unless $x$ lies in the open corner simplex, where every $\theta_i$ is positive and
$\theta_i^+ = \theta_i$.
