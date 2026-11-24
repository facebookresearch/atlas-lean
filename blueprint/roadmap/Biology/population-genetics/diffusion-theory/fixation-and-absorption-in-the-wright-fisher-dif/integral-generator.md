# Dynkin's formula at a fixed time

Let $\mu$ be a finite measure on a measurable space $\Omega$, $(\mathcal{F}_t)_{t \ge 0}$ a
filtration, $\sigma$ a real number and $(X_t)_{t \ge 0}$ a
[solution of the Wright–Fisher martingale problem](is-wright-fisher-solution.md) with scaled
selection coefficient $\sigma$ with respect to $(\mathcal{F}_t)$ and $\mu$. Then for every twice
continuously differentiable $f : \mathbb{R} \to \mathbb{R}$ and every time $t \ge 0$, the function
$\omega \mapsto \int_0^t (L_\sigma f)(X_s(\omega))\, ds$ is $\mu$-integrable and

$$
\int_\Omega \int_0^t (L_\sigma f)(X_s)\, ds\, d\mu
= \int_\Omega f(X_t)\, d\mu - \int_\Omega f(X_0)\, d\mu,
$$

where $L_\sigma$ is the [backward generator](../wright-fisher-diffusion/generator.md). When $\mu$ is a
probability measure, this says $\mathbb{E}\bigl[\int_0^t (L_\sigma f)(X_s)\, ds\bigr] =
\mathbb{E}[f(X_t)] - \mathbb{E}[f(X_0)]$.
