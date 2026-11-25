# Quasi-stationary law of the neutral Wright–Fisher diffusion

Let $K_t$ be the [neutral Wright–Fisher kernel](../wright-fisher-semigroup-and-moment-duality/wf-transition-kernel.md) on $[0, 1]$, the diffusion with generator $\frac12x(1 - x)\partial_x^2$ and absorbing endpoints, and write $g(x) = x(1 - x)$. For a probability measure $\mu$ on $[0, 1]$ set $c(\mu) = \int g\,d\mu$, so that $c(\mu) > 0$ exactly when $\mu$ charges the interior $(0, 1)$, and let $s_t(\mu) = \int K_t(x, (0, 1))\,\mu(dx)$ be the probability that neither allele is fixed at time $t$. Then:

1. The uniform law on $(0, 1)$ is quasi-stationary: started from it, $s_t = e^{-t}$ and the law of $X_t$ given $X_t \in (0, 1)$ is again uniform, for every $t > 0$.
2. For every $\mu$ with $c(\mu) > 0$, as $t \to \infty$,

    $$s_t(\mu) = c(\mu)\bigl(6e^{-t} + O(e^{-6t})\bigr),$$

    so the survival probability decays at rate $1$ with the coefficient $6c(\mu)$ determined by the initial law.
3. For the same $\mu$, the conditional law of $X_t$ given $X_t \in (0, 1)$ converges to the uniform law on $(0, 1)$, with total variation distance $O(e^{-2t})$; the uniform law is the Yaglom limit, whatever the interior initial law.

Since the endpoints are absorbing, $X_t \in (0, 1)$ is the event that the process has not been fixed at $0$ or $1$ during $(0, t]$. Griffiths, Jenkins and Spanò (2017, Section 2) obtain this Yaglom density as the first orthogonal polynomial times the speed density, which for $\theta_1 = \theta_2 = 0$ is the constant $1$ on $(0, 1)$.

## Depends on

- [The neutral Gegenbauer series identifies the Wright–Fisher kernel](../wright-fisher-diffusion/identification-of-the-kimura-series-with-the-neu.md)
- [Convergence and PDEs of the neutral Gegenbauer series](../wright-fisher-diffusion/kimura-1955-eigen-series-convergence-and-pde-for.md)
- [Spatial and time integrals of the neutral spectral series](../wright-fisher-diffusion/distribution-of-absorption-time-from-the-spectra.md)
- [Transition kernel of the neutral Wright–Fisher diffusion](../wright-fisher-semigroup-and-moment-duality/wf-transition-kernel.md)

## Expansion

1. On $(0, 1)$ the kernel has the density $p_t(x, y)$ of the Gegenbauer series, so $s_t(\mu) = \int S_t\,d\mu$ with $S_t(x) = \int_0^1 p_t(x, y)\,dy$, and the conditional law has density $\int p_t(x, \cdot)\,\mu(dx)/s_t(\mu)$.
2. Started from the uniform law, $\int_0^1 p_t(x, y)\,dx = e^{-t}$ for all $y$: integrating each term against $dx$ leaves only the first, because $\int_0^1 g(x)C_{i-1}^{(3/2)}(1 - 2x)\,dx = 0$ for $i \ge 2$ by orthogonality of the Gegenbauer polynomials for the weight $g$, while the first term contributes $\frac{4 \cdot 3}{2}\cdot\frac16\,e^{-t} = e^{-t}$.
3. The uniform expansions $S_t(x) = g(x)(6e^{-t} + O(e^{-6t}))$ and $p_t(x, y) = g(x)(6e^{-t} + O(e^{-3t}))$, with remainders bounded by $g(x)$ times a constant independent of $x$ and $y$, integrate against $\mu$ to the survival asymptotics and give, for every Borel $A \subseteq (0, 1)$, a conditional probability $|A| + O(e^{-2t})$ uniformly in $A$.

## Sources

- R. C. Griffiths, P. A. Jenkins and D. Spanò, Wright–Fisher diffusion bridges, arXiv:1703.00208, Section 2 (the Yaglom density as the limit density given no fixation in $(0, t)$, equal to $1$ on $(0, 1)$ when $\theta_1 = \theta_2 = 0$). <https://arxiv.org/abs/1703.00208>
