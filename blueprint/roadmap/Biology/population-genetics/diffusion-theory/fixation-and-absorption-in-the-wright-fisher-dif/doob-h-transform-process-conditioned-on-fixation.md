# Doob h-transform: the Wright–Fisher diffusion conditioned on fixation

Let $\alpha \in \mathbb R$, let $X$ solve the [martingale problem for the Wright–Fisher diffusion](is-wright-fisher-solution.md) with genic selection,

$$L f(x) = \tfrac12 x(1 - x) f''(x) + \alpha x(1 - x) f'(x),$$

without mutation, started at $p \in (0, 1)$, and let $u_\alpha$ be the [fixation probability](measure-real-fixation.md), the solution of $L u_\alpha = 0$ with $u_\alpha(0) = 0$, $u_\alpha(1) = 1$. Under $\mathbb P(\,\cdot \mid \text{fixation})$, $X$ solves the martingale problem for

$$L^{\mathrm{fix}} f(x) = \tfrac12 x(1 - x) f''(x) + \Bigl(\alpha x(1 - x) + x(1 - x)\frac{u_\alpha'(x)}{u_\alpha(x)}\Bigr) f'(x);$$

in the neutral case $\alpha = 0$, $u_0(x) = x$ and the conditioned drift is $1 - x$. Consequently the mean absorption time conditioned on fixation is

$$\mathbb E_p[\tau \mid \text{fixation}] = \int_0^1 G_D(p, x)\, \frac{u_\alpha(x)}{u_\alpha(p)}\, dx,$$

where $G_D(p, x) = G(p, x)\, m(x)$ is the Lebesgue occupation density of the [occupation-time formula](../sojourn-times-of-the-wright-fisher-diffusion/occupation-time-formula-and-mean-absorption-time.md): the scale Green kernel $G$ times the speed density $m$.

## Depends on

- [Martingale problem for the Wright–Fisher diffusion](is-wright-fisher-solution.md)
- [Kimura's fixation probability, process form](measure-real-fixation.md)
- [Occupation-time formula and mean absorption time with selection](../sojourn-times-of-the-wright-fisher-diffusion/occupation-time-formula-and-mean-absorption-time.md)

## Proof depends on

- [Localized h-transform for nonnegative harmonic h (conditioning on fixation)](localized-h-transform-for-nonnegative-harmonic-h.md)
- [Martingale problems (generic definition)](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md)

## Expansion

A full proof page must still establish:

- the conditioned martingale problem, by the [localized h-transform](localized-h-transform-for-nonnegative-harmonic-h.md) with $h = u_\alpha$;
- the conditioned Lebesgue occupation density $G_D(p, x)\, u_\alpha(x)/u_\alpha(p)$, with $G_D = G\, m$ as in the occupation-time formula, and the formula for the conditional mean absorption time;
- the neutral case.

## Sources

- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer, 2004, conditioned processes, <https://doi.org/10.1007/978-0-387-21822-9>
- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press, 1981, Chapter 15
