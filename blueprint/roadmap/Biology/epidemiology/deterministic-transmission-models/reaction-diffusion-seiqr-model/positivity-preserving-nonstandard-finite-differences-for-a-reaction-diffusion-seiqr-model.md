# Positivity-preserving nonstandard finite differences for a reaction–diffusion SEIQR model

**Model.** On a bounded domain $\Omega \subset \mathbb{R}^2$ with homogeneous Neumann boundary conditions, susceptible, exposed, infected, quarantined and recovered densities evolve by

$$\begin{aligned}
\partial_tS &= \lambda_S\Delta S + \Lambda + \rho Q - \beta_1SE - \beta_2SI - \mu S,\\
\partial_tE &= \lambda_E\Delta E + \beta_1SE - (\delta + \mu)E,\\
\partial_tI &= \lambda_I\Delta I + \beta_2SI + \delta E - (\gamma + \mu)I,\\
\partial_tQ &= \lambda_Q\Delta Q + \gamma I - (\alpha + \rho + \mu)Q,\\
\partial_tR &= \lambda_R\Delta R + \alpha Q - \mu R,
\end{aligned}$$

with recruitment $\Lambda$, natural death $\mu$, transmission from exposed ($\beta_1$) and infected ($\beta_2$) individuals, progression $\delta$, quarantine $\gamma$, recovery $\alpha$ from quarantine and return $\rho$ of quarantined individuals to the susceptible class.

**Theorem (well-posedness).** For positive initial data the system has a unique global solution $\psi = (S,E,I,Q,R)$ on $\mathcal{U} = (0,T)\times\Omega$ that stays positive and bounded, with

$$\psi_i \in W^{1,2}(0,T;L^2(\Omega)) \cap L^2(0,T;H^2(\Omega)) \cap L^\infty(0,T;H^1(\Omega)) \cap L^\infty(\mathcal{U}).$$

**Theorem (NSFD scheme).** On a uniform grid with time step $k$, space step $h$ and $r = k/h^2$ fixed, discretize each equation with nonlocal approximations of the nonlinear and loss terms (evaluating losses at the new time level) and replace the time step by the denominator function

$$\phi_\ell(k) = k\Big(1 - 4\lambda_\ell\frac{k}{h^2} - k\mu - g_\ell(k)\Big)^{-1}, \qquad g_S = k(\beta_1E^n_{j,l} + \beta_2I^n_{j,l}),\ g_E = k\delta,\ g_I = k\gamma,\ g_Q = k(\alpha + \rho),\ g_R = 0.$$

Under the step restrictions $|k\mu + g_\ell(k)| < |1 - 4r\lambda_\ell|$, the scheme is consistent of order $1$ in time and $2$ in space, and its explicit update writes each new value as a nonnegative combination of old values and positive sources, so positivity and boundedness are preserved, which standard explicit schemes can violate.

## Expansion

Global existence follows from local existence for semilinear parabolic systems together with a priori bounds: the total population $N = S + E + I + Q + R$ satisfies a linear reaction–diffusion inequality with source $\Lambda$ and decay $\mu$, bounding all components in $L^\infty$, and maximal regularity then gives the Sobolev estimates. Mickens-type NSFD design puts negative (loss) terms implicitly and positive terms explicitly, so that, for example, $S^{n+1}_{j,l}(1 + k\mu + g_S) = S^n_{j,l} + k(\text{diffusion} + \Lambda + \rho Q^n)$ keeps $S^{n+1} \ge 0$; the nonstandard denominator absorbs the diffusion stencil weight $4r\lambda_\ell$. Taylor expansion of the scheme around the exact solution gives the local truncation error $O(k + h^2)$.

## Sources

- A. Zinihi, M. Ehrhardt and M. R. Sidi Ammi, "A Nonstandard Finite Difference Scheme for an SEIQR Epidemiological PDE Model", *Applied Mathematics and Computation* 520 (2026), 129953, System (2.1)–(2.3), Theorems 1 and 2, <https://doi.org/10.1016/j.amc.2026.129953> (preprint arXiv:2508.02928).
