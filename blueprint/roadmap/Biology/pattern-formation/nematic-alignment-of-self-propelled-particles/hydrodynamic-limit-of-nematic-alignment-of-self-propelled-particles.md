# Hydrodynamic limit of nematic alignment of self-propelled particles

**Kinetic model.** Self-propelled particles in the plane move at unit speed in direction $v(\theta) = (\cos\theta,\sin\theta)$ and align *nematically* with their neighbours: a particle turns towards the local mean axis $\bar\theta_f$ (an angle of lines, defined modulo $\pi$ by $\int \sin 2(\theta - \bar\theta_f)\,f\,d\theta = 0$), choosing whichever orientation along the axis is closer, with angular noise. In the hydrodynamic scaling the one-particle density $f^\varepsilon(x,\theta,t)$ solves

$$\varepsilon\big(\partial_t f^\varepsilon + \nabla_x\cdot(v(\theta)f^\varepsilon)\big) = Q^0_{\rm al}f^\varepsilon, \qquad Q^0_{\rm al}f = \partial_\theta\Big[\operatorname{sign}\!\big(\cos(\theta-\bar\theta_f)\big)\sin(\theta-\bar\theta_f)\,f + D\cos^2(\theta-\bar\theta_f)\,\partial_\theta f\Big],$$

with $\kappa = 1/D$. The equilibria of $Q^0_{\rm al}$ are exactly

$$\bar f_{\rho_+,\rho_-,\bar\theta}(\theta) = M_{\bar\theta}(\theta)\big[\rho_+\mathbf 1_{\cos(\theta-\bar\theta)>0} + \rho_-\mathbf 1_{\cos(\theta-\bar\theta)<0}\big], \qquad M_{\bar\theta}(\theta) \propto e^{-\kappa/|\cos(\theta-\bar\theta)|},$$

parametrized by the densities $\rho_\pm \ge 0$ of particles moving parallel and anti-parallel to the axis $\bar\theta$: the set of equilibria is three-dimensional although only mass is conserved.

**Theorem (formal hydrodynamic limit).** As $\varepsilon \to 0$, $f^\varepsilon \to \bar f_{\rho_+,\rho_-,\bar\theta}$, where

$$\partial_t\rho_+ + d_1\nabla_x\cdot\big(\rho_+v(\bar\theta)\big) = 0, \qquad \partial_t\rho_- - d_1\nabla_x\cdot\big(\rho_-v(\bar\theta)\big) = 0,$$

$$(\rho_+ + \rho_-)\,\partial_t\bar\theta + d_2(\rho_+ - \rho_-)\big(v(\bar\theta)\cdot\nabla_x\big)\bar\theta + \mu\,v(\bar\theta)^\perp\cdot\nabla_x(\rho_+ - \rho_-) = 0,$$

with $d_1 = \langle\cos\rangle_M$ and $d_2$, $\mu$ explicit ratios of $M$-averages of the generalized collision invariant $g$, where $\langle\varphi\rangle_M = \frac{2}{Z_\kappa}\int_0^{\pi/2}\varphi(\theta)e^{-\kappa/\cos\theta}\,d\theta$. This system is hyperbolic but non-conservative.

**Weakly non-local interactions.** If alignment is computed over a small but finite neighbourhood, the $\bar\theta$ equation acquires the diffusive right-hand side $2k\,\mathcal D\,\nabla_x\cdot\big((\rho_+ + \rho_-)\nabla_x\bar\theta\big)$ with $\mathcal D = d_2 + d_3 - \mu - 2/\kappa \ge 0$ for all $\kappa \ge 0$. Adding reversals of direction at density-dependent rates $\lambda(\rho_\pm)$, as in myxobacteria, adds the exchange terms $\pm\big(\lambda(\rho_+)\rho_- - \lambda(\rho_-)\rho_+\big)$ to the density equations.

## Expansion

Integrating the kinetic equation over $\theta$ on each half-circle would give conservation of $\rho_+$ and $\rho_-$ only if the collision operator conserved them, and no third invariant exists for $\bar\theta$. The generalized collision invariants (GCI) fix this: for each axis $\theta_0$ the space of functions $\psi$ with $\int Q^0_{\rm al}(f)\,\psi = 0$ for all $f$ with $\bar\theta_f = \theta_0$ is three-dimensional, spanned by the half-circle indicators $\chi^\pm_{\theta_0}$ and a function $g_{\theta_0}$ solving an elliptic problem. Multiplying by these and passing to the limit yields the two density equations and the axis equation, with coefficients given by averages of $g$ against $M$.

## Sources

- Pierre Degond, Angelika Manhart and Hui Yu, "A continuum model for nematic alignment of self-propelled particles", arXiv:1509.03124 (2015), Lemma 3.7 (equilibria), Proposition 3.11 (generalized collision invariants), Theorem 4.1 and Lemma 4.2 (hydrodynamic limit and hyperbolicity), Theorem 5.3 and Lemma 5.4 (weakly non-local limit and positive diffusion), Proposition 6.1 (myxobacteria), <https://doi.org/10.48550/arXiv.1509.03124>.
