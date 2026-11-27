# Lipschitz envelope of the score derivative

Let $\sigma \ge 0$ and $c > 0$, and let $\theta = (a, b)$ and $\theta_0 = (a_0, b_0)$ have all four
coordinates at least $c$. Then for every count $k$ the [score derivative matrix](count-hessian.md)
$H_\sigma(\theta, k)$ satisfies

$$
\bigl\| H_\sigma(\theta, k) - H_\sigma(\theta_0, k) \bigr\|
\le \Bigl(\frac{6}{c^2} + \frac{4 (|a_0| + k)}{c^3}\Bigr) \|\theta - \theta_0\|,
$$

with the operator norm on the left: the Lipschitz constant is affine in the count $k$.
