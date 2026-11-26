# Linear instability criterion for density-suppressed aggregation

**Setting.** Consider the mean-field aggregation equation

$$\partial_t\varrho=\tfrac12\Delta\big(G(W*\varrho)^2\varrho\big)$$

on $\mathbb R^d$ or a periodic box, with a nonincreasing motility function $G$ and an integrable sensing kernel $W$ normalized by $\int W=1$. Let $\varrho_0>0$ be a constant state with $G(\varrho_0)>0$ and $G'(\varrho_0)<0$.

**Proposition.** Linearizing at $\varrho_0$, a perturbation with Fourier transform $\hat\varrho(t,\xi)$ obeys

$$\partial_t\hat\varrho+|\xi|^2\frac{G(\varrho_0)}2\Big(G(\varrho_0)+2G'(\varrho_0)\varrho_0\,\hat W(\xi)\Big)\hat\varrho=0 .$$

Hence the mode $\xi$ is linearly stable if and only if

$$\operatorname{Re}\hat W(\xi)<-\frac{G(\varrho_0)}{2G'(\varrho_0)\varrho_0}\quad(>0).$$

Since $\hat W\in C_0(\mathbb R^d)$, all sufficiently high wavenumbers are stable, and aggregation patterns grow from low wavenumbers violating the inequality. For a rescaled kernel $W_r(x)=r^{-d}W_1(x/r)$, $\hat W_r(\xi)=\hat W_1(r\xi)$, so the pattern wavelength scales with the sensing radius $r$.

**Local limit.** For $W=\delta_0$ the condition becomes $(G(\varrho_0)^2\varrho_0)'>0$; when it fails, the local equation $\partial_t\varrho=\tfrac12\nabla\cdot\big(G(\varrho)[2G'(\varrho)\varrho+G(\varrho)]\nabla\varrho\big)$ is backward parabolic and ill-posed. Nonlocal sensing keeps the diffusivity $G(W*\varrho)^2$ positive and moves the instability into a well-posed transport term.

## Expansion

Expanding $G(W*\varrho)^2=G(\varrho_0)^2+2\varepsilon G(\varrho_0)G'(\varrho_0)W*\tilde\varrho+O(\varepsilon^2)$ and keeping first-order terms gives the linear equation; the Fourier multiplier is a negative-diffusion contribution $2G'\varrho_0\hat W$ competing with ordinary diffusion $G$. High modes are damped fast while the slower unstable low modes build aggregates, which then coarsen: in simulations the smaller of two clumps dissolves into the larger.

## Depends on

- [Mean-field limit of density-suppressed random walks](mean-field-limit-of-density-suppressed-random-walks.md)

## Sources

- M. Burger, J. Haškovec, M.-T. Wolfram, "Individual based and mean-field modeling of direct aggregation", *Physica D* (2013), Section 4.4, equations (4.9)–(4.12), <https://doi.org/10.1016/j.physd.2012.11.003>, PMCID: PMC4047626.
