# Circle integrals of functions of the square vanish

For every function $f : \mathbb{C} \to \mathbb{C}$ and every $R \in \mathbb{R}$, the circle integral of $z \mapsto f(z^2)$ along the path $z = R e^{i\theta}$, $0 \le \theta \le 2\pi$, vanishes:

$$\int_0^{2\pi} i R e^{i\theta} f\bigl(R^2 e^{2i\theta}\bigr)\, d\theta = 0.$$

For $R < 0$ the path runs over the circle of radius $|R|$, starting at $R$. The integral is taken to be $0$ when its integrand $\theta \mapsto i R e^{i\theta} f(R^2 e^{2i\theta})$ is not integrable on $[0, 2\pi]$; for such $f$ the identity holds by this convention. The integrand is antiperiodic with antiperiod $\pi$, so when it is integrable the integrals over $[0, \pi]$ and $[\pi, 2\pi]$ cancel.
