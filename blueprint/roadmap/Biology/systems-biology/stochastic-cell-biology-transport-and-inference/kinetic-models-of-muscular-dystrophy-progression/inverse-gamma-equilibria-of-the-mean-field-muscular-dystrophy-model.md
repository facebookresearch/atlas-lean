# Inverse-gamma equilibria of the mean-field model of muscular dystrophy

Across a large cohort of patients, let $f_J(x,t)$ be the distribution of the density $x \ge 0$ of cells of type $J \in \{N, D, M, C\}$: normal muscle fibers, damaged fibers, macrophages, and cytotoxic T lymphocytes. Each $f_J$ has unit mass and mean $m_J(t) = \int x f_J\, dx$. A quasi-invariant scaling of a kinetic (Boltzmann-type) model of cell interactions gives the mean-field Fokker–Planck system

$$
\begin{aligned}
\partial_t f_N &= \partial_x\big[(\beta_N m_C x - \beta_D m_M m_D) f_N\big] + \tfrac{\sigma_N^2 m_C}{2}\partial_x^2(x^2 f_N), \\
\partial_t f_D &= \partial_x\big[(\beta_D m_M x - \beta_N m_N m_C) f_D\big] + \tfrac{\sigma_D^2 m_M}{2}\partial_x^2(x^2 f_D), \\
\partial_t f_M &= \partial_x\big[(\beta_M x - \gamma_M m_D) f_M\big] + \tfrac{\sigma_M^2}{2}\partial_x^2(x^2 f_M), \\
\partial_t f_C &= \partial_x\big[(\beta_C x - \gamma_C m_M) f_C\big] + \tfrac{\sigma_C^2}{2}\partial_x^2(x^2 f_C),
\end{aligned}
$$

on $\mathbb{R}_+$ with no-flux boundary conditions at $x = 0$. Here cytotoxic T cells damage normal fibers, macrophages clear damaged fibers, and damaged fibers and macrophages recruit macrophages and T cells, respectively.

**Theorem (long-time asymptotics).** Suppose the initial data $f_J(0,\cdot)$ are probability densities with bounded means and variances satisfying the paper's compatibility conditions, and $\|f_J(0,\cdot) - f_J^\infty\|_{\dot H_{-p}} < \infty$ for some $\tfrac12 < p < 1$. Then

$$
\sum_{J \in \{N, D, M, C\}} \|f_J(t) - f_J^\infty\|_{\dot H_{-p}} \to 0 \quad (t \to \infty), \qquad \tfrac12 < p < 1,
$$

where each equilibrium is an inverse-gamma density

$$
f_J^\infty(x) = \frac{(\omega_J^\infty)^{\nu_J}}{\Gamma(\nu_J)}\, x^{-\nu_J - 1} e^{-\omega_J^\infty/x}, \qquad \nu_J = 1 + \frac{2\beta_J}{\sigma_J^2},
$$

with $\omega_N^\infty = \frac{2\beta_D\beta_C}{\sigma_N^2\gamma_C}m_D^\infty$, $\omega_D^\infty = \frac{2\beta_N\gamma_C}{\sigma_D^2\beta_C}m_N^\infty$, $\omega_M^\infty = \frac{2\gamma_M}{\sigma_M^2}m_D^\infty$, $\omega_C^\infty = \frac{2\gamma_C\gamma_M}{\sigma_C^2\beta_M}m_D^\infty$, and $m_J^\infty$ the limits of the means.

## Expansion

Multiplying the equations by $x$ and integrating gives a closed ODE system for the means $m_J(t)$. Its solutions converge, so asymptotically each equation becomes a linear Fokker–Planck equation with drift $\beta x - c$ and diffusion $\propto x^2$. Such an equation has an inverse-gamma steady state; its heavy right tail reflects patients with extreme cell densities. Quasi-equilibria $f_J^q(t)$, built from the current means and variances, converge to $f_J^\infty$ uniformly. The solution itself is compared with them in the homogeneous negative Sobolev norm $\dot H_{-p}$, which is defined through Fourier transforms and well suited to Fokker–Planck equations with $x^2$ diffusion.

## Sources

- Tommaso Lorenzi, Horacio Tettamanti, Mattia Zanella, "Kinetic and Mean‐Field Modeling of Muscular Dystrophies", Studies in Applied Mathematics 157 (2026), e70316, <https://doi.org/10.1111/sapm.70316>. Published version of arXiv:2511.15599, cited next; locators there refer to the arXiv version.
- Tommaso Lorenzi, Horacio Tettamanti, Mattia Zanella, "Kinetic and mean-field modeling of muscular dystrophies", arXiv (2025). Section 2 (kinetic and mean-field models), Section 3, Theorem 3.1 and the explicit equilibria. <https://doi.org/10.48550/arXiv.2511.15599>
