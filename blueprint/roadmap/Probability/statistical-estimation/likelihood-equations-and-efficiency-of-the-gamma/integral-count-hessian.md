# Minus the expected score derivative is the Fisher information

Let $\mu_X$ be a probability measure on $\mathbb{N}$, the law of a count $K$, and write $E$ for
expectations under $\mu_X$. Let $\theta_0 = (a, b)$ with $a, b > 0$, let $\sigma \ge 0$, and let $K$
be integrable with the marginal mean of the hierarchy, $E K = \sigma a / b$. Then the expected
[score derivative matrix](count-hessian.md) $H_\sigma(\theta, k)$ at $\theta_0$ is minus the
[Fisher information matrix](count-fisher-info.md):

$$E\bigl[H_\sigma(\theta_0, K)\bigr] = -I(a, b, \sigma, \tau_0), \qquad \tau_0 = E[\varphi_K(a)],$$

with the [trigamma increment](trigamma-increment.md) $\varphi_k(a) = \sum_{j < k} 1/(a + j)^2$; in
particular $I_{ab} = -\sigma / (b (b + \sigma))$ and $I_{bb} = a \sigma / (b^2 (b + \sigma))$.
