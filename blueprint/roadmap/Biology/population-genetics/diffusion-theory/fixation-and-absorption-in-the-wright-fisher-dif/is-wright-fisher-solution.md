# Martingale problem for the Wright–Fisher diffusion

Let $\sigma$ be real, $(\mathcal{F}_t)_{t \ge 0}$ a filtration on a measurable space $\Omega$ and $\mu$ a measure on $\Omega$. A real process $(X_t)_{t \ge 0}$ solves the martingale problem for the Wright–Fisher diffusion with scaled genic selection coefficient $\sigma = 2Ns$, time in units of $2N$ generations, if $X$ takes values in $[0, 1]$, has continuous paths, is adapted to $(\mathcal{F}_t)$, and for every twice continuously differentiable $f : \mathbb{R} \to \mathbb{R}$ the process

$$f(X_t) - f(X_0) - \int_0^t (L_\sigma f)(X_s)\, ds$$

is an $(\mathcal{F}_t)$-martingale under $\mu$, where $L_\sigma$ is the [backward generator](../wright-fisher-diffusion/generator.md).
