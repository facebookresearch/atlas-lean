# Linear instability of homogeneous base states under concentration-dependent growth

For the one-dimensional [concentration-dependent growing-domain model](concentration-dependent-domain-evolution-model.md) with $m = 2$ species, define the spatially homogeneous base state $(u^*(t), \mu^*(t))$ by

$$\frac{d\mu^*}{dt} = S(t,u^*)\mu^*, \qquad \frac{du^*}{dt} = -S(t,u^*)u^* + f(u^*), \qquad f(u^*(0)) = 0,\ \mu^*(0) = 1 .$$

Perturb $u = u^* + \varepsilon U$, $\mu = \mu^* + \varepsilon\nu$. To first order,

$$\frac{\partial\nu}{\partial t} = S\nu + \mu^*\,\nabla_uS\cdot U, \qquad \frac{\partial U}{\partial t} = \frac{D}{(\mu^*)^2}\frac{\partial^2U}{\partial X^2} + M(t)U, \qquad M = J - K - S(t,u^*)I,$$

with $J_{ij} = \partial f_i/\partial u_j(u^*)$ and $K_{ij} = u_i^*\,\partial S/\partial u_j(t,u^*)$. The $U$-equation does not involve $\nu$, so perturbations of the domain do not affect the linear stability of homogeneous states. Expanding $U = \sum_k\psi_k(X)V_k(t)$ in Neumann eigenfunctions $\psi_k = \cos(k\pi X/L)$, $\rho_k = (k\pi/L)^2$, each mode obeys the non-autonomous system

$$\frac{dV_k}{dt} = \big(-\rho_k(\mu^*(t))^{-2}D + M(t)\big)V_k, \qquad \mu^*(t) = \exp\Big(\int_0^tS(s,u^*(s))\,ds\Big).$$

A sufficient condition for exponential growth of mode $k$ on a time interval $I_k$ (when $M$ is not diagonal) is the differential inequality of Van Gorder (2020, Theorem 2.1) applied to this system. The new term relative to prescribed growth is $K$, the concentration dependence of the growth rate; for slow growth the criteria reduce to quasi-static corrections of the classical Turing conditions. In $N > 1$ dimensions with the potential-flow closure, growth is non-uniform even for constant $S$, the eigenfunctions are no longer separable, and this reduction fails.

## Depends on

- [Reaction–diffusion on a domain whose growth depends on the concentrations](concentration-dependent-domain-evolution-model.md)
- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Expansion

Differentiating $\mu_t = \mu S(t,u)$ at $(\mu^*, u^*)$ gives $\nu_t = S(t,u^*)\nu + \mu^*\nabla_uS(t,u^*)\cdot U$. Since $u^*$ is spatially homogeneous, every term multiplying $\nu$ carries a spatial derivative of $u^*$ and vanishes; linearizing $-uS(t,u)$ gives $-SU - (\nabla_uS\cdot U)u^* = -SU - KU$. The Laplace–Beltrami operator in Lagrangian coordinates is $(\mu^*)^{-2}\partial_X^2$ because the base metric is spatially uniform, so the time dependence factors out of the spatial eigenproblem and modes decouple.

## Sources

- Andrew L. Krause, Eamonn A. Gaffney and Benjamin J. Walker, "Concentration-Dependent Domain Evolution in Reaction–Diffusion Systems", Bulletin of Mathematical Biology (2023), <https://doi.org/10.1007/s11538-022-01115-2> (PMC9839823). Section 3, Eqs. (16)–(22) and Theorem 1 (quoted from R. A. Van Gorder, Proc. R. Soc. A 2020).
