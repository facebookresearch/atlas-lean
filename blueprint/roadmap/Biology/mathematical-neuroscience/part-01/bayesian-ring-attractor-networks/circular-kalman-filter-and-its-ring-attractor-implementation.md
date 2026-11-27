# Circular Kalman filter and its ring attractor implementation

**Generative model.** A head direction $\phi_t \in [-\pi, \pi)$ diffuses on the circle with prior angular-velocity precision $\kappa_\phi$. Angular-velocity observations in a small step $\delta t$ are Gaussian, $v_t \mid \phi_t, \phi_{t - \delta t} \sim \mathcal{N}\bigl((\phi_t - \phi_{t-\delta t})/\delta t,\ 1/(\kappa_v \delta t)\bigr)$, and direction observations are von Mises, $z_t \mid \phi_t \sim \mathcal{VM}(\phi_t, \kappa_z \delta t)$.

**Circular Kalman filter.** Approximating the posterior by a von Mises law $\mathcal{VM}(\mu_t, \kappa_t)$ and projecting the filtering equations onto that family gives, in continuous time,

$$d\mu_t = \frac{\kappa_v}{\kappa_\phi + \kappa_v}\, v_t\, dt + \frac{\kappa_z}{\kappa_t} \sin(z_t - \mu_t)\, dt,$$

$$d\kappa_t = -\frac{f(\kappa_t)\, \kappa_t}{2(\kappa_\phi + \kappa_v)}\, dt + \kappa_z \cos(z_t - \mu_t)\, dt,$$

with $A(\kappa) = I_1(\kappa)/I_0(\kappa)$ ($I_0, I_1$ modified Bessel functions) and $f$ an increasing nonlinearity built from $A$ that satisfies $f(\kappa) \to 2\kappa - 2$ as $\kappa \to \infty$. In the high-certainty regime this gives the quadratic decay

$$d\kappa_t \approx -\frac{\kappa_t^2 - \kappa_t}{\kappa_\phi + \kappa_v}\, dt + \kappa_z \cos(z_t - \mu_t)\, dt .$$

**Vector picture.** Represent the belief as the vector $\kappa_t (\cos\mu_t, \sin\mu_t)$. A direction observation adds the vector $\kappa_z\, \delta t\, (\cos z_t, \sin z_t)$: this is exact Bayes, since the product of von Mises densities $\mathcal{VM}(\mu, \kappa)\,\mathcal{VM}(z, \kappa_z\delta t)$ is von Mises with parameter vector equal to the sum. Its projections onto the belief direction and its normal give the $\cos$ and $\sin$ terms above, so consistent observations increase certainty and conflicting ones decrease it. Angular-velocity observations rotate the vector and, with the diffusion prior, shorten it.

**Network implementation.** A rate network with $N \to \infty$ neurons with preferred directions $\phi_i$, leak time constant $\tau$, recurrent weights $W(v_t) = w_{\mathrm{const}} \mathbf{1}\mathbf{1}^\top/N + w_{\mathrm{sym}} W^{\cos} + w_{\mathrm{asym}}(v_t)\, W^{\sin}$ with $W^{\cos}_{ij} = \tfrac{2}{N}\cos(\phi_i - \phi_j)$, $W^{\sin}_{ij} = \tfrac{2}{N}\sin(\phi_i - \phi_j)$, a global activity-dependent decay $g(r_t)$, and cosine input $I_t \cos(\Phi_t - \phi_i)$, encodes $(\mu_t, \kappa_t)$ in the phase and amplitude of its first Fourier mode, which evolve as

$$d\mu_t = w_{\mathrm{asym}}(v_t)\, dt + \frac{I_t}{\kappa_t} \sin(\Phi_t - \mu_t), \qquad d\kappa_t = \Bigl(w_{\mathrm{sym}} - \frac1\tau\Bigr)\kappa_t\, dt - g(r_t)\, \kappa_t\, dt + I_t \cos(\Phi_t - \mu_t).$$

These match the circular Kalman filter exactly when $w_{\mathrm{asym}}(v_t) = \kappa_v v_t/(\kappa_\phi + \kappa_v)$, $I_t = \kappa_z\, dt$ with $\Phi_t = z_t$, $w_{\mathrm{sym}} = 1/\tau$, and $g(r_t) = f(\kappa(r_t))/(2(\kappa_\phi + \kappa_v))$, i.e. global inhibition that grows with bump amplitude.

## Expansion

The drift of $\mu_t$ uses the posterior mean of the angular velocity, $\kappa_v v_t/(\kappa_\phi + \kappa_v)$, from combining the prior precision $\kappa_\phi$ with the observation precision $\kappa_v$; the residual uncertainty makes the direction diffuse with variance rate $1/(\kappa_\phi + \kappa_v)$, and for a concentrated von Mises law ($\mathrm{Var} \approx 1/\kappa$) this gives $d(1/\kappa) \approx dt/(\kappa_\phi + \kappa_v)$, i.e. the quadratic decay $\dot\kappa \approx -\kappa^2/(\kappa_\phi + \kappa_v)$. A classical ring attractor keeps a fixed bump amplitude, so it cannot represent certainty; with the parameters above the amplitude grows with confirmatory input and shrinks with conflicting input or in darkness, and in the quadratic regime one can take $w_{\mathrm{sym}} - 1/\tau = 1/(\kappa_\phi + \kappa_v)$ and inhibition linear in amplitude, $g = \kappa/(\kappa_\phi + \kappa_v)$, so without input the amplitude relaxes to a fixed value and the network is again an attractor network (a Bayesian ring attractor) whose amplitude reflects the balance between evidence and diffusion.

## Sources

- A. Kutschireiter, M. A. Basnak, R. I. Wilson, J. Drugowitsch, "Bayesian inference in ring attractor networks", Proceedings of the National Academy of Sciences of the USA 120 (2023) e2210622120, Results (Equations 1–2) and Methods (Equations 8–13, "Network parameters for Bayesian inference"), <https://doi.org/10.1073/pnas.2210622120> (PMC9992764).
