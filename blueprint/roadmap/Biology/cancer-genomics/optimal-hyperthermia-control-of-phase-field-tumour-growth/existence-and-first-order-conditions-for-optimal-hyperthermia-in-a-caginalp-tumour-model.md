# Existence and first-order conditions for optimal hyperthermia in a Caginalp-type tumour model

**State system.** On a smooth bounded domain $\Omega\subset\mathbb{R}^d$ with $Q = \Omega\times(0,T)$, let $\theta$ be the relative temperature, $\phi \in [-1,1]$ the tumour/healthy phase field ($\phi = 1$ tumour, $\phi = -1$ healthy), $\mu$ the chemical potential and $\sigma$ the nutrient concentration. For a heat source (thermal therapy) $u$ they solve

$$\partial_t(\theta + \ell\phi) - \Delta\theta = u,$$

$$\partial_t\phi - \Delta\mu = (\lambda_p\sigma - \lambda_a - \lambda_e\theta)\,h(\phi),$$

$$\mu = \tau\partial_t\phi - \Delta\phi + \beta(\phi) + \pi(\phi) - \chi\sigma - \Lambda\theta,$$

$$\partial_t\sigma - \Delta(\sigma - \chi\phi) = -\lambda_c\sigma h(\phi) + \lambda_b(\sigma_B - \sigma) - \lambda_d\sigma k(\theta),$$

with homogeneous Neumann conditions and initial data $\theta_0 \in H^1\cap L^\infty$, $\phi_0 \in H^3$ with $\partial_\nu \phi_0 = 0$, and $\sigma_0 \in H^1$. Here $\ell, \Lambda, \chi > 0$; $\tau \ge 0$, so the Cahn–Hilliard part may be viscous or not; the rates $\lambda_\bullet \ge 0$; $\sigma_B \in L^2(Q)$; $h, k$ are bounded, nonnegative, Lipschitz and $C^2$; and $\beta + \pi$ is the derivative of a double-well potential with convex part $\hat\beta$ and Lipschitz-derivative perturbation $\hat\pi$. For every $u$ with $\|u\|_{L^\infty(Q)} < M$ the system has a unique strong solution, and the control-to-state map is Lipschitz.

**Control problem.** Minimize

$$\mathcal{J}(u) = \frac{b_1}{2}\int_Q|\theta - \theta_Q|^2 + \frac{b_2}{2}\int_\Omega|\theta(T) - \theta_\Omega|^2 + \frac{b_3}{2}\int_Q|\phi-\phi_Q|^2 + \frac{b_4}{2}\int_\Omega|\phi(T) - \phi_\Omega|^2 + \frac{b_5}{2}\int_Q|u|^2$$

over $\mathcal{U}_{\rm ad} = \{u \in L^\infty(Q) : u_{\min}\le u\le u_{\max}\ \text{a.e.}\}$, with $b_1,\dots,b_4 \ge 0$, $b_5 > 0$, $\theta_Q,\phi_Q\in L^2(Q)$ and $\theta_\Omega,\phi_\Omega \in H^1(\Omega)$.

**Theorem.**

1. An optimal control $u^* \in \mathcal{U}_{\rm ad}$ exists.
2. The control-to-state operator is Fréchet differentiable. Its derivative in direction $h$ is the solution of the linearized system.
3. If $u^*$ is optimal, the adjoint system has a unique weak solution $(z, p, q, r)$, and for every $u \in \mathcal{U}_{\rm ad}$

$$\int_Q (z + b_5 u^*)(u - u^*)\,dx\,dt \ge 0 .$$

Equivalently, $u^*$ is the pointwise projection of $-z/b_5$ onto $[u_{\min}, u_{\max}]$.

## Expansion

Existence follows from the direct method: a minimizing sequence in the bounded, weak-star closed set $\mathcal{U}_{\rm ad}$ has states that are bounded in the strong-solution spaces. These states converge strongly by Aubin–Lions compactness, and the cost is weakly lower semicontinuous. Differentiability uses the $L^\infty(Q)$ bound on $\phi$, which makes the potential locally Lipschitz along trajectories. Testing the linearized system against the adjoint variables and integrating in time removes the linearized states from the directional derivative of $\mathcal{J}$, which yields the variational inequality. The Caginalp coupling $\partial_t(\theta+\ell\phi)$ and the term $-\Lambda\theta$ in $\mu$ let heating act on the tumour phase. The term $-\lambda_e\theta h(\phi)$ models heat-induced tumour cell death.

## Sources

- G. Cavalleri, P. Colli and E. Rocca, "Optimal control for a fourth-order nonisothermal tumor growth model of Caginalp type", arXiv:2604.24108 (2026), hypotheses (H1)–(H6), Theorems 4.1, 4.2, 6.1, 7.2 and 7.3, <https://doi.org/10.48550/arXiv.2604.24108>.
