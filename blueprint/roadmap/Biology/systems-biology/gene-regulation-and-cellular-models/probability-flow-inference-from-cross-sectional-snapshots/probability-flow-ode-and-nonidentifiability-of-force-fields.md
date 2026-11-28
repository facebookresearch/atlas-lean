# Probability flow ODE and non-identifiability of force fields

Let cell states $x \in \mathbb{R}^d$ (for example gene expression) follow the Itô SDE $dx = f(x)\,dt + \sqrt{2}\,G(x)\,dW$ with force field $f$, intrinsic noise model $G$ and diffusion tensor $D = GG^{\mathsf T}$. Single-cell omics provides only **cross-sectional snapshots**: independent samples from the marginals $p_t$ at a few times, with no trajectories. The marginals obey the Fokker-Planck equation

$$\partial_t p_t = -\nabla \cdot \big[f\, p_t - \nabla \cdot (D\, p_t)\big].$$

**Probability flow.** The deterministic ODE

$$\frac{dx}{dt} = f(x) - \nabla \cdot D(x) - D(x)\, \nabla \log p_t(x),$$

started from $x(0) \sim p_0$, has the same marginals $p_t$ as the SDE for all $t \ge 0$. Hence a force can be fit to snapshots by estimating the score $\nabla \log p_t$ and pushing samples forward with this ODE instead of simulating the SDE.

**Non-identifiability.** With $D$ and $p_0$ fixed, a force $f + h$ produces the same marginals as $f$ whenever

$$\nabla \cdot \big(h(x)\, p_t(x)\big) = 0 \quad \text{for all } t \ge 0 \text{ and all } x.$$

For example, if every $p_t$ is radially symmetric about the origin, then $h(x) = Kx$ with any skew-symmetric matrix $K$ satisfies this, so rotational (non-conservative) force components are invisible to the marginals. In addition, $f$ and $D$ cannot both be inferred from snapshots, so a prior on the noise model is required.

## Expansion

Writing the Fokker-Planck equation as a continuity equation $\partial_t p_t + \nabla\cdot(v_t p_t) = 0$ with velocity $v_t = f - \nabla\cdot(D p_t)/p_t = f - \nabla\cdot D - D\nabla\log p_t$ (for symmetric $D$) shows that the ODE transports $p_0$ along the same path of marginals. Adding $h$ changes the right side by $-\nabla\cdot(h p_t)$, which vanishes under the stated condition, so the marginal path is unchanged. For radially symmetric $p_t(x) = \pi_t(|x|)$, $\nabla\cdot(Kx\,p_t) = p_t\, \mathrm{tr} K + (Kx)\cdot x\, \pi_t'(|x|)/|x| = 0$ because $\mathrm{tr}K = 0$ and $x^{\mathsf T}Kx = 0$. In practice the ill-posedness is removed by regularizing the force (for example an $\ell_2$ penalty on its Jacobian), and the noise model is fixed from biophysics, such as the state-dependent diffusion of the chemical Langevin approximation of a reaction network.

## Sources

- S. Maddu, V. Chardès, M. J. Shelley, "Learning stochastic processes with intrinsic noise from cross-sectional biological data", Proceedings of the National Academy of Sciences of the USA (2025), Section 2 (Eqs. 1-7: SDE, Fokker-Planck equation, probability flow ODE, identifiability condition Eq. 6, regularized loss Eq. 7), Analytical case study (OU process, Theorem 1, Eq. 8; isotropic process and approximate minimizer). <https://doi.org/10.1073/pnas.2420621122> (PMC12452938)
