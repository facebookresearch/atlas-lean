# Growth-rate variance of a phenotype-switching population in a Markov environment

**Model.** A population consists of phenotypes $x \in \mathcal{X}$ with sizes $N_x$. The environment $s(t)$ is a continuous-time Markov chain on a finite set $\mathcal{S}$ with jump rates $\kappa_{s|s'}$. Phenotype $x$ grows at rate $k(x|s)$ in environment $s$ and individuals switch phenotype blindly (independently of $s$) with rates $\pi(x|y)$:

$$\dot N_x = k(x|s(t))N_x - \pi_x N_x + \sum_{y \ne x}\pi(x|y)N_y.$$

In terms of the total $N = \sum_x N_x$ and fractions $\phi_x = N_x/N$, $\frac{d}{dt}\log N = f_{\mathrm{growth}}(\phi; s) := \sum_x k(x|s)\phi_x$, and $(\phi, s)$ is a piecewise-deterministic Markov process with generator $\mathcal{L}$ (flow $\dot\phi = v(\phi|s)$ between environment jumps) and stationary law $\mathbb{P}$. The Lyapunov exponent $\lambda = \lim_T \frac1T\log(N(T)/N(0)) = (\mathbb{P}, f_{\mathrm{growth}})$ is deterministic; the *asymptotic growth-rate variance* is $\mathrm{var}(\lambda) = \lim_T \frac1T\mathrm{Var}\log(N(T)/N(0))$.

**Theorem (general formula).** With $\delta f = f_{\mathrm{growth}} - \lambda$,

$$\mathrm{var}(\lambda) = 2\big((-\mathcal{L})^{-1}\delta f,\ \delta f\big)_{\mathbb{P}},$$

and, for every mean-zero $f$,

$$\tfrac12\big((-\mathcal{L})^{-1}f, f\big)_{\mathbb{P}} = \sup_a\Big\{(f, a)_{\mathbb{P}} - \tfrac12\big((-\mathcal{L}_{\mathrm{sym}})^{-1}\mathcal{L}^\dagger a,\ \mathcal{L}^\dagger a\big)_{\mathbb{P}}\Big\},$$

where $\mathcal{L}^\dagger$ is the $\mathbb{P}$-adjoint and $\mathcal{L}_{\mathrm{sym}}$ the symmetric (environment-jump) part, whose Dirichlet form is $\frac12\int d\phi\sum_{s\ne s'}\kappa_{s|s'}\mathbb{P}_{s'}(\phi)(f_s(\phi) - f_{s'}(\phi))^2$.

**Theorem (two phenotypes, two environments).** Let $\phi = \phi_1$, $\Delta_s = k(1|s) - k(2|s)$ with $\Delta_1 > 0 > \Delta_2$ (phenotype $s$ is fitter in environment $s$), and $v_s(\phi) = \Delta_s\phi(1-\phi) - \pi_1\phi + \pi_2(1-\phi)$. The stationary densities $\mathbb{P}_1, \mathbb{P}_2$ are supported on $(\phi_2^+, \phi_1^+)$, the interval between the stable fixed points of the two flows, and satisfy $v_1\mathbb{P}_1 + v_2\mathbb{P}_2 = 0$. With

$$I(\phi) = \int_{\phi_2^+}^{\phi}\big(\mathbb{P}_1\,\delta f_1 + \mathbb{P}_2\,\delta f_2\big)(\phi')\,d\phi', \qquad q(\phi) = \frac{(v_1\mathbb{P}_1)^2(\phi)}{\kappa_1\mathbb{P}_1(\phi) + \kappa_2\mathbb{P}_2(\phi)},$$

the asymptotic growth-rate variance is

$$\mathrm{var}(\lambda) = \int_{\phi_2^+}^{\phi_1^+} \frac{I(\phi)^2}{q(\phi)}\,d\phi.$$

## Proof sketch

$\log N(T) = \int_0^T f_{\mathrm{growth}}(\phi(t); s(t))\,dt$ is an additive functional of an ergodic Markov process, so its variance growth rate is given by the Green–Kubo formula $2\int_0^\infty \mathrm{Cov}_{\mathbb{P}}(\delta f(\Phi_0), \delta f(\Phi_t))\,dt = 2((-\mathcal{L})^{-1}\delta f, \delta f)_{\mathbb{P}}$. The variational formula is the standard dual representation for non-reversible generators. In the two-state case the Poisson equation $-\mathcal{L}u = \delta f$ reduces, using $v_1\mathbb{P}_1 = -v_2\mathbb{P}_2$, to a first-order ODE for $u_1 - u_2$ that integrates explicitly, giving the closed form; this quantifies the risk (fluctuation) side of the trade-off between mean fitness $\lambda$ and its variance in bet-hedging strategies.

## Sources

- Jérémie Unterberger, "Exact Computation of Growth-Rate Variance in Randomly Fluctuating Environment", *Journal of Statistical Physics* 189 (2022), 37, <https://doi.org/10.1007/s10955-022-03002-5>. Preprint version: arXiv:2111.04167 (2021), Section 2 (variance formula, variational formula, symmetric part) and Section 3 (explicit formula in the two-state model), <https://doi.org/10.48550/arXiv.2111.04167>.
