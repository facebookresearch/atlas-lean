# Reaction–diffusion on a domain whose growth depends on the concentrations

Let $u = (u_1,\dots,u_m)$ be morphogen concentrations on a compact evolving domain $\Omega(t) \subset \mathbb R^N$ with smooth boundary and no-flux boundary conditions. Conservation of mass in the Lagrangian frame $X \in \Omega(0)$ gives

$$\frac{\partial u}{\partial t} = D\nabla^2_{\Omega(t)}u - u\,\nabla_{\Omega(t)}\cdot a + f(u),$$

with $D = \operatorname{diag}(D_1,\dots,D_m)$, kinetics $f$, material flow $a$, and, in terms of the metric tensor $G_{ij} = \frac{\partial x}{\partial X_i}\cdot\frac{\partial x}{\partial X_j}$ pulled back to Lagrangian coordinates ($H = G^{-1}$, $\mu = \sqrt{|\det G|}$), the Laplace–Beltrami operator of $G$ and the flow divergence

$$\nabla^2_{\Omega(t)}u = \frac1\mu\sum_{i,j}\frac{\partial}{\partial X_i}\Big(\mu H^{ij}\frac{\partial u}{\partial X_j}\Big), \qquad \nabla_{\Omega(t)}\cdot a = \frac{\partial}{\partial t}\log\mu .$$

Domain evolution is a local isotropic expansion at a concentration-dependent rate: $\partial_t\log\mu = S(t,u)$, $\mu(0,X) = 1$.

**One dimension.** With $X \in [0,L]$, $G_{11} = (\partial x/\partial X)^2$, so $\mu = \partial x/\partial X$ (orientation preserved), $G_{11} = \mu^2$ and $H^{11} = \mu^{-2}$, and the system closes:

$$\frac{\partial u}{\partial t} = \frac{D}{\mu}\frac{\partial}{\partial X}\Big(\frac1\mu\frac{\partial u}{\partial X}\Big) - uS(t,u) + f(u), \qquad \frac{\partial}{\partial t}\log\mu = S(t,u),$$

and material points move as $x(t,X) = \int_0^X\exp\big(\int_0^tS(s,u(s,y))\,ds\big)\,dy$, so $\Omega(t) = [0, x(t,L)]$.

**Higher dimensions.** $\partial_t\log\mu = S$ does not determine $G$. Assume the flow is irrotational, $a = \nabla_{\Omega(t)}\phi$, and impose as an explicit closure the Dirichlet condition $\phi = 0$ on $\partial\Omega(t)$, so that

$$\nabla^2_{\Omega(t)}\phi = S(t,u) \ \text{in } \Omega(t), \qquad \phi = 0 \ \text{on } \partial\Omega(t), \qquad \partial_tx = \nabla_{\Omega(t)}\phi,$$

which together with the concentration equation is a closed system in the Lagrangian frame (for $N = 2$, $H$ and $\mu$ are expressed through $\partial x/\partial X_1$, $\partial x/\partial X_2$). The Dirichlet condition makes the boundary flow normal; normal boundary flow alone would only make $\phi$ constant on each boundary component, possibly with different constants (on an annulus, $\phi = c\log r$ has normal gradient on both circles but different boundary values), so it does not by itself give the closure. Taking $S = S(t)$ recovers prescribed domain growth.

## Depends on

- [Laplace–Beltrami operator](../../../Geometry/riemannian-geometry/laplace-beltrami-operator/laplacian.md)

## Expansion

Reynolds' transport theorem for $\int_{\omega(t)}u\,dx$ over a material subdomain, pulled back to $\Omega(0)$ with Jacobian $\mu$, gives $\partial_t(\mu u) = \mu(D\nabla^2u + f)$; expanding $\partial_t(\mu u)$ yields the dilution term $-u\,\partial_t\log\mu$. In 1D the metric is the scalar $G_{11} = \mu^2$, so the growth law fixes the geometry; in higher dimensions an extra constitutive choice (here a potential flow) is needed to fix the shear part of $G$.

## Sources

- Andrew L. Krause, Eamonn A. Gaffney and Benjamin J. Walker, "Concentration-Dependent Domain Evolution in Reaction–Diffusion Systems", Bulletin of Mathematical Biology (2023), <https://doi.org/10.1007/s11538-022-01115-2> (PMC9839823). Section 2, Eqs. (1)–(15).
