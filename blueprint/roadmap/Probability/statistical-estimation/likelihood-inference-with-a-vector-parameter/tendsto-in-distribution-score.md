# Central limit theorem for the score vector

Let $E$ be a finite-dimensional real inner product space, $\nu$ a measure, $p_\theta$ ($\theta \in E$) densities with respect to $\nu$, $P_\theta = p_\theta\,\nu$, $s_\theta = \nabla_\theta\log p_\theta$ the score and $I(\theta)$ the Fisher information operator. Let $X_0, X_1, \dots$ be mutually independent observations with law $P_{\theta_0}$, $s_{\theta_0}$ measurable with mean zero and finite second moment, and $Y$ a random vector with $\langle Y, t\rangle \sim \mathcal N(0, \langle I(\theta_0)t, t\rangle)$ for every $t$. Then $n^{-1/2}\sum_{i<n}s_{\theta_0}(X_i)$ converges in distribution to $Y$. The information may be singular.

## Sources

- Lehmann & Casella (1998), §6.5; van der Vaart (1998), ch. 5.
