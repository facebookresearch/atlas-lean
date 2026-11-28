# Flux-limited glioma invasion system and its invariant unit box

**Macroscopic system.** A multiscale derivation (single-cell receptor binding, a kinetic transport equation for glioma cells with velocity and receptor-occupancy variables, then a Hilbert expansion under hyperbolic scaling) leads, for the glioma density $M$, normal tissue $Q$, acidity (proton concentration) $h$ and endothelial cells $e$, all nondimensionalized to $[0,1]$, to

$$
\begin{aligned}
\partial_t M + \nabla\cdot\big(g(y^*)\,M\big) &= \eta(h, s^*)\,\big(y^* - (y^*)^2\big)\,M(1 - M),\\
\partial_t Q &= c_1 Q(1 - Q - M) - c_2\,\frac{h}{1 + h}\,Q,\\
\partial_t h &= D_h \Delta h + \gamma(1 - h)\,\frac{M}{1 + M} - \delta h e,\\
\partial_t e &= D_e \Delta e - \varsigma_e \nabla\cdot\big(e(1 - e)\nabla h\big) + G_e(h, M)\,e(1 - e),
\end{aligned}
$$

where $y^* = \kappa Q/(\kappa Q + 1)$ is the equilibrium fraction of cell receptors bound to tissue fibers and the glioma velocity field is

$$
g(y^*) = \frac{a_1}{a_2 s_{\max}}(1 - M)\,\mathbb{D}_W\, b(y^*), \qquad b(y^*) = (1 - \rho_1 - \rho_2)\frac{-\nabla h}{\sqrt{1 + |\nabla h|^2}} + \rho_1 (1 - y^*)\frac{\nabla Q}{\sqrt{1 + |\nabla Q|^2}} + \rho_2 \frac{-\nabla M}{\sqrt{1 + |\nabla M|^2}},
$$

with $\mathbb{D}_W$ the (symmetric positive semidefinite) water diffusion tensor from diffusion tensor imaging, $\rho_1, \rho_2 \ge 0$, $\rho_1 + \rho_2 \le 1$. The glioma flux thus combines **flux-limited** self-diffusion, repellent pH-taxis and haptotaxis: each gradient enters through $\nabla\phi/\sqrt{1 + |\nabla\phi|^2}$, so the transport speed stays bounded however steep the gradients are. All fluxes vanish on the boundary of a bounded smooth domain $\Omega$ (no-flux conditions).

**Lemma (degenerate comparison principle).** Let $u \in \mathbb{R}$ and let $M \in C^{1,2}((0,T)\times\Omega)$ solve

$$
M_t = \nabla\cdot\big(a(t,x,M,\nabla M)(u - M)\nabla M\big) + \nabla\cdot\big(b(t,x,M,\nabla M)(u - M)\big) + c(t,x,M)
$$

with zero flux $\big(a(u - M)\nabla M + b(u - M)\big)\cdot\nu = 0$ on $\partial\Omega$ and $M(0, \cdot) \le u$, where $a$ (matrix-valued) and $b$ are $C^1$, $\xi^\top a\,\xi \ge 0$, $c$ is continuous, Lipschitz in $M$ near $u$ and $c(t,x,u) = 0$. Then $M \le u$ on $(0,T)\times\Omega$.

**Lemma (invariant unit box).** Every classical solution $(M, Q, h, e)$ of the macroscopic system with no-flux boundary conditions and initial data in $[0,1]^4$ satisfies $0 \le M, Q, h, e \le 1$ for all $(t,x) \in (0,T)\times\Omega$.

## Expansion

The density-dependent factor $(1 - M)$ in the velocity (volume filling) and the factor $e(1 - e)$ in the haptotactic flux make the diffusion and taxis coefficients degenerate exactly at the upper bound $1$, so the ordinary parabolic maximum principle does not apply directly. The comparison lemma handles this: the degenerate factor $(u - M)$ kills the transport terms at the level $u$, and the Lipschitz reaction with $c(\cdot,\cdot,u) = 0$ prevents crossing, via a Gronwall argument on the positive part $(M - u)_+$. Applying it with $u = 1$ to $M$ and $e$, using the logistic structure of their sources, and the standard scalar maximum principle to the reaction-diffusion equation for $h$ and to the ODE for $Q$, gives the invariant box. The flux limitation reflects that cells cannot move faster than a maximal speed $s_{\max} = a_1\alpha_{\max}/a_2$ set by the largest eigenvalue $\alpha_{\max}$ of $\mathbb{D}_W$, in contrast with linear diffusion, which propagates at infinite speed.

## Proof depends on

- [Gronwall inequality in integral form](../../../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Sources

- Anne Dietrich, Niklas Kolbe, Nikolaos Sfakianakis and Christina Surulescu, "Multiscale modeling of glioma invasion: from receptor binding to flux-limited macroscopic PDEs", arXiv (2020), section "Derivation of a fully macroscopic system" (macroscopic system and coefficients, degenerate comparison principle Lemma 1.2, boundedness Lemma 1.4), <https://doi.org/10.48550/arXiv.2010.03277>.
