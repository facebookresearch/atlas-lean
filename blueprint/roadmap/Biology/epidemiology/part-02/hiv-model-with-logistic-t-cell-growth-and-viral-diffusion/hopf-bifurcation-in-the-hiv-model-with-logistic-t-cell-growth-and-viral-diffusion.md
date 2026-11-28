# Hopf bifurcation in the HIV model with logistic T-cell growth and viral diffusion

**Setting.** Consider, on $(0,\ell)^2$ with periodic boundary conditions for the virus,

$$\frac{\partial T}{\partial t} = \alpha - \mu_T T + rT\Big(1 - \frac{T}{T_{\max}}\Big) - \gamma VT, \qquad \frac{\partial I}{\partial t} = \gamma VT - \mu_I I, \qquad \frac{\partial V}{\partial t} = N\mu_I I - \mu_V V + d_V \Delta V,$$

with $\mu_I > \mu_T$ and $T_{\max}$ large. In the infected region $\mathcal{I}$ of the $(N, r)$ plane the spatially constant infected equilibrium $\mathbf{X}_i(N,r)$ is stable outside a set $\mathcal{P} = \{N \ge N_{2,0},\ r_{1,0}(N) \le r \le r_{2,0}(N)\}$ and unstable inside it. For large $T_{\max}$,

$$N_{2,0} = \frac{\mu_I^2 + 3\mu_I\mu_V + \mu_V^2 + 2\sqrt{\mu_I\mu_T\mu_V(\mu_I + \mu_V)}}{\gamma\mu_I}\,\frac{1}{T_{\max}} + o(T_{\max}^{-1}).$$

**Theorem (Hopf bifurcation).** Fix $N \ge N_{2,0}$ and let $T_{\max}$ be large enough. Taking the logistic rate $r$ as the bifurcation parameter, a Hopf bifurcation occurs at each boundary point $r = r_j$ ($j = 1, 2$, where $r_1 = r_{1,0}(N)$, $r_2 = r_{2,0}(N)$): for every $\beta \in (0,1)$ there are smooth families $\varepsilon \mapsto (\hat r_j(\varepsilon), \rho_j(\varepsilon), \mathbf{X}_{\sharp,j}(\varepsilon))$, with $\hat r_j(0) = r_j$, $\rho_j(0) = 1$ and $\mathbf{X}_{\sharp,j}(0) = \mathbf{X}_i(r_j)$, of solutions that are periodic and non-constant in time for $\varepsilon \ne 0$, with period $2\pi\rho_j(\varepsilon)/\omega_j$, where

$$\omega_j = \sqrt{\alpha\gamma N + \frac{\alpha\gamma\mu_I N}{\mu_V} + \frac{\mu_V r_j}{\gamma N T_{\max}}(\mu_I + \mu_V)}.$$

Locally these are the only periodic solutions near $(\mathbf{X}_i(r_j), r_j)$ up to time translation, and the bifurcating periodic solutions are independent of the space variables.

**Theorem (stability of the cycles).** For $T_{\max}$ large enough:

1. if $N < N_*$, where $N_*$ is the first positive zero of an explicit quintic polynomial $\mathcal{H}(N)$ in the model parameters (with $\mathcal{H}(0) < 0$ and $\mathcal{H}(N) \to +\infty$), arising from the centre-manifold reduction, the periodic solutions bifurcating at $r_1$ are orbitally asymptotically stable with asymptotic phase;
2. for every $N > 0$, the periodic solutions bifurcating at $r_2$ are orbitally asymptotically stable with asymptotic phase.

Biologically, inside $\mathcal{P}$ the T-cell, infected-cell and virus levels oscillate in time instead of settling to the infected steady state.

## Depends on

- [Stability of equilibria in the HIV model with logistic T-cell growth and viral diffusion](stability-of-equilibria-in-the-hiv-model-with-logistic-t-cell-growth-and-viral-diffusion.md)

## Expansion

The system is only partially dissipative ($T$ and $I$ do not diffuse), so the resolvent of the linearization is not compact. The proof uses instead that the linearization generates an analytic semigroup, which is enough for the Hopf bifurcation theorem in infinite dimensions. At $r = r_j$ the zero mode has a simple pair of purely imaginary eigenvalues $\pm i\omega_j$ crossing the axis transversally, while every nonzero Fourier mode stays strictly stable because the sets $\mathcal{P}_k$ for $k \ge 1$ lie inside $\mathcal{P}$. The stability of the cycles is read off a centre manifold: the spectral projections onto the eigenvalues $\pm i\omega_j$ reduce the problem to a planar normal form, whose first Lyapunov coefficient fixes the direction of bifurcation.

## Sources

- C.-M. Brauner, X. Fan and L. Lorenzi, "Two-dimensional stability analysis in a HIV model with quadratic logistic growth term", arXiv:1211.0136 (2012), Section 4: Theorem 4.1 (Hopf bifurcation at the boundary of $\mathcal{P}$) and Theorem 4.3 (orbital stability of the bifurcating periodic solutions). <https://doi.org/10.48550/arXiv.1211.0136>. Published version: Communications on Pure and Applied Analysis 12(5) (2013), 1813–1844, <https://doi.org/10.3934/cpaa.2013.12.1813>; locators above refer to the arXiv version.
