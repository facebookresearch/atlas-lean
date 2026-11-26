# Unique steady state and Hopf bifurcations in the ZIP transporter model

**Model.** Zinc uptake in *Arabidopsis thaliana* roots is regulated by ZIP transporters whose gene is induced by a dimerizing activator, which is in turn sequestered by a zinc-sensing inhibitor. With transcription and translation quasi-stationary, the non-dimensional state $u = (u_1, u_2, u_3, u_4)$ (gene activity / transporter level, internal zinc, activator, inhibitor) satisfies

$$\frac{du_1}{dt} = \kappa u_3^2 (1 - u_1) - u_1, \qquad \frac{du_2}{dt} = u_1 f(\mu) - u_2,$$

$$\frac{du_3}{dt} = 1 - \gamma_1 u_3 u_4 - u_3, \qquad \frac{du_4}{dt} = \gamma_2 u_2 - \gamma_3 u_3 u_4 - (1 + \gamma_2 u_2) u_4,$$

where $f(\mu) = \mu/(\mu + K)$ is the zinc influx at external zinc concentration $\mu \ge 0$, and $\kappa, K, \gamma_1, \gamma_2, \gamma_3 > 0$.

**Theorem (well-posedness and steady state).** For every initial value in $\mathcal{S} = [0,1]^4$ there is a unique global solution, and it stays in $\mathcal{S}$. For every positive parameter set there is exactly one steady state $u^*(\mu)$ in $\mathcal{S}$; it lies in the interior, depends smoothly on $\mu > 0$, and its third component $u_3^*$ is the unique root in $\big(\tfrac{1}{1+\gamma_1}, 1\big)$ of the quartic

$$\phi(x) = \gamma_3\kappa x^4 + \big(f\gamma_2(1+\gamma_1) + 1 - \gamma_3\big)\kappa x^3 + \big(\gamma_3 - \kappa - f\gamma_2\kappa\big)x^2 + (1 - \gamma_3)x - 1, \qquad f = f(\mu).$$

The Jacobian determinant at $u^*$ is strictly positive.

**Theorem (Hopf bifurcations, fitted parameters).** For the fitted values $K = 13$, $\kappa = 20$, $\gamma_1 = 380$, $\gamma_2 = 1000$, $\gamma_3 = 1672$ and $\mu \in [0, 30]$, the steady state $u^*(\mu)$ undergoes Hopf bifurcations at two critical external zinc concentrations $\mu_1 \approx 0.19$ and $\mu_2 \approx 12.6$: a complex pair of eigenvalues of the Jacobian crosses the imaginary axis transversally at each, while the other two eigenvalues stay real and negative. Both bifurcations are supercritical, with stable orbits arising for $\mu > \mu_1$ and for $\mu < \mu_2$. A continuous path of periodic orbits connects the two Hopf points, $(u^*(\mu_1), \mu_1)$ being a source and $(u^*(\mu_2), \mu_2)$ a sink in the sense of the Alexander–Yorke / Mallet-Paret–Yorke global Hopf theory, and the orbits are asymptotically stable.

## Expansion

Eliminating $u_1, u_2, u_4$ at equilibrium reduces the steady-state problem to the scalar quartic $\phi(u_3) = 0$; sign changes of $\phi$ on the interval and positivity of the Jacobian determinant give existence, uniqueness and smooth dependence on $\mu$. The Hopf part is computer-assisted: the steady-state branch is continued numerically, the eigenvalue crossings and the first Lyapunov coefficients come from the normal form on a two-dimensional center manifold, boundedness of solutions and parameter and numerically computed bounded periods force the global branch to end at the second Hopf point, and Floquet multipliers computed from the monodromy matrix (one equal to $1$, the rest in $(0,1)$) show stability. Biologically the stable oscillations produce potentially toxic zinc peaks; adding a zinc buffer can restore stability of the steady state.

## Sources

- J. Claus, M. Ptashnyk, A. Bohmann and A. Chavarría-Krauser, "Global Hopf Bifurcation in the ZIP regulatory system", arXiv:1401.5597 (2014), model in Section 2 with its existence and unique-steady-state theorems (proofs in Appendix, Lemmas B.1–B.2), local Hopf theorem in Section 3, normal form in Section 4, global continuation theorem in Section 5 and Floquet stability in Section 6, <https://doi.org/10.48550/arXiv.1401.5597>.
