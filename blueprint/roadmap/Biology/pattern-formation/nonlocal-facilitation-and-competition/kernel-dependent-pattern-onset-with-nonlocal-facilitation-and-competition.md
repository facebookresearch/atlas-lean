# Kernel-dependent pattern onset with nonlocal facilitation and competition

**Model.** A population density $u(x,t)$, $x \in \mathbb{R}$, grows with saturating nonlocal facilitation and nonlocal competition:

$$\partial_t u = g\,u\Bigl(1 - c + \frac{f_{\max}\,\mathcal{K}_f * u}{f_{\max}/f_0 + \mathcal{K}_f * u}\Bigr)\Bigl(1 - \frac{\mathcal{K}_c * u}{M}\Bigr) - du + k_d\,\partial_x^2 u,$$

with growth rate $g$, cost of facilitation $c$, carrying capacity $M$, death rate $d$, motility $k_d$, and normalized kernels $\mathcal{K}_{f,c}(x) = \sigma^{-1}\tilde{\mathcal{K}}_{f,c}(x/\sigma)$; $\sigma_f = 1$, so $\sigma_c$ is the ratio of competition to facilitation range. For $d$ below a tipping value $d_{\mathrm{tip}}$ (a saddle-node of the uniform dynamics) there is a stable positive uniform state $u_*$.

**Dispersion relation.** Linearizing at $u_*$, with $t_0, t_1$ the zeroth and first Taylor coefficients of $f_{\max}u/(f_{\max}/f_0 + u)$ at $u_*$, Fourier modes $e^{i\omega x}$ grow at rate

$$\hat{\mathcal{L}}(\omega) = g\,u_*\Bigl(t_1\bigl(1 - \tfrac{u_*}{M}\bigr)\hat{\mathcal{K}}_f(\omega) - \frac{1 - c + t_0}{M}\hat{\mathcal{K}}_c(\omega)\Bigr) - k_d\omega^2 .$$

**Proposition (bifurcation in the competition range).** For Gaussian-like kernels and fixed $0 < d < d_{\mathrm{tip}}$: for $\sigma_c$ small enough, $\hat{\mathcal{L}} < 0$ for all $\omega$ and $u_*$ is linearly stable; this holds already at $\sigma_c = 1$ if $\hat{\tilde{\mathcal{K}}}_f \le \hat{\tilde{\mathcal{K}}}_c$; and for small enough $k_d$ there are $\sigma_* > 1$ and $\omega_* > 0$ with $\hat{\mathcal{L}}_{\sigma_*}(\omega_*) > 0$, so long-range competition destabilizes $u_*$ at a finite wavelength. Hat-like (compact) kernels behave the same way.

**Proposition (bifurcation in mortality).** For fixed $\sigma_c > 1$: at $d = 0$ the uniform state is stable, while for small $k_d$ some $0 < d_* < d_{\mathrm{tip}}$ and $\omega_* > 0$ give $\hat{\mathcal{L}}_{d_*}(\omega_*) > 0$, so patterns appear under stress before the uniform tipping point.

## Depends on

- [Squared critical wavenumber](../turing-patterns-and-diffusion-driven-instability/critical-wavenumber-sq.md)

## Expansion

This is a nonlocal analogue of short-range activation and long-range inhibition: facilitation (positive weight $\hat{\mathcal{K}}_f$) and competition (negative weight $\hat{\mathcal{K}}_c$) act at different ranges, and when $\sigma_c > 1$ the competition transform decays faster in $\omega$, so at intermediate frequencies facilitation can win. Diffusion damps high frequencies, which is why small $k_d$ is needed. The sign structure of the Fourier transforms is what distinguishes kernels: Gaussian transforms are positive, while top-hat transforms oscillate in sign, changing which frequencies are selected and how patterns persist beyond onset.

## Sources

- O. Clifton, S. Dodson, D. B. Cooney, "Kernel-Dependent Pattern Formation in a Population Model with Nonlocal Facilitation and Competition" (2026), model (e:main), linearization (e:lin) and Propositions 1-3, <https://doi.org/10.48550/arXiv.2608.23964>.
