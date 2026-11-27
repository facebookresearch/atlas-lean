# Non-equilibrium allele frequency spectrum

Let $\xi_t$ be the Wright–Fisher diffusion with scaled selection coefficient $\gamma \in \mathbb{R}$,

$$ d\xi_t = \gamma \xi_t (1-\xi_t)\, dt + \sqrt{\xi_t(1-\xi_t)}\, dW_t , $$

with fixation time $\tau_1$, fixation probability $q_\gamma(x) = (1-e^{-2\gamma x})/(1-e^{-2\gamma})$ ($q_0(x) = x$), and let $\mathbb{P}^{*\gamma}_x$ denote its law conditioned on fixation. Put $\omega_\gamma = 2\gamma/(1-e^{-2\gamma})$ ($\omega_0 = 1$), $\pi_0(y) = 2/y$ and $\pi_\gamma(y) = (1-e^{-2\gamma(1-y)})/(\gamma y (1-y))$, so that $\theta\omega_\gamma\pi_\gamma(y)\,dy$ is the stationary Poisson random field intensity.

Start a population of size $N$ at time $0$ in a completely monomorphic state; new mutations arrive as a Poisson process of rate $N\theta$ per unit of diffusion time, each starting at frequency $1/N$ and evolving independently. Let $\mathcal{X}^N_t$ be the resulting random field of derived-allele frequencies, and let $\mathcal{F}_0$ be the bounded $f$ on $[0,1]$ with $f(0)=f(1)=0$ and $\int_0^1 y^{-1}|f(y)|\,dy < \infty$. Then for every $t \ge 0$ and $f \in \mathcal{F}_0$

$$ \lim_{N\to\infty} \mathbb{E}\langle \mathcal{X}^N_t, f\rangle = \theta\omega_\gamma \int_0^1 f(y)\, \mathbb{P}^{*\gamma}_{1-y}(\tau_1 \le t)\, \pi_\gamma(y)\, dy = \theta \int_0^1 f(y)\, \frac{\mathbb{P}^{\gamma}_{1-y}(\tau_1 \le t)}{1-y}\, \pi_0(y)\, dy . $$

Thus the time-$t$ spectrum is the stationary spectrum $\theta\omega_\gamma\pi_\gamma(y)$ weighted by the probability that a diffusion started at $1-y$ and conditioned to fix has done so by time $t$; it increases to the stationary spectrum as $t\to\infty$. For bounded $f$ with $f(0) = 0$ but $f(1) \neq 0$ an extra term $\theta f(1)\omega_\gamma t$ accounts for mutations fixed by time $t$.

## Depends on

- [Expected site frequency spectrum under the Poisson random field](expected-sfs.md)
- [Sawyer–Hartl Poisson random field density](prf-density.md)

## Expansion

By Campbell's formula $\mathbb{E}\langle\mathcal{X}^N_t,f\rangle = N\theta\,\mathbb{E}^\gamma_{1/N}\int_0^{t\wedge\tau} f(\xi_u)\,du$. As $N\to\infty$, $N\,\mathbb{E}^\gamma_{1/N}\int_0^{\tau}f(\xi_u)\,du \to \omega_\gamma\int_0^1 f\pi_\gamma$ (scaled occupation time). Restricting to $[0,t]$ is handled by time reversal: a diffusion started near $0$ and conditioned to fix, read backwards, looks like a diffusion started at $1-y$ conditioned to fix, so the occupation density at $y$ accumulated by time $t$ picks up the factor $\mathbb{P}^{*\gamma}_{1-y}(\tau_1 \le t)$. The two forms agree because $\mathbb{P}^{*\gamma}_{1-y}(\tau_1\le t) = \mathbb{P}^{\gamma}_{1-y}(\tau_1\le t)/q_\gamma(1-y)$ and $\omega_\gamma\pi_\gamma(y)/q_\gamma(1-y) = \pi_0(y)/(1-y)$.

## Sources

- Ingemar Kaj and Carina F. Mugal, *The non-equilibrium allele frequency spectrum in a Poisson random field framework*, Theor. Popul. Biol. 111 (2016), 51–64. <https://doi.org/10.1016/j.tpb.2016.06.003> Section 2 (Poisson random field model; Propositions 1 and 2) and Section 3.1, Theorem 1. Locators use the numbering of the preprint arXiv:1512.04925.
