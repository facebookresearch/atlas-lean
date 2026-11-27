# Perceptual kernels and nonlocal resource-perception advection

Let $m(x,t)$ be a resource density on a spatial domain $\Omega$. A perceptual kernel (detection function) with perceptual range $R\ge0$ is a function $g$ that is (i) symmetric about the origin, (ii) normalised, $\int_\Omega g=1$, (iii) concentrates to $\delta$ as $R\to0^+$, and (iv) non-increasing in distance from the origin. Standard one-dimensional examples on $\Omega=\mathbb R$ are

$$g(z)=\frac{1}{2R}\mathbf 1_{[-R,R]}(z),\qquad g(z)=\frac{1}{\sqrt{2\pi}R}e^{-z^2/2R^2},\qquad g(z)=\frac{1}{2R}e^{-|z|/R},$$

the top-hat, Gaussian and exponential kernels. The perception function is

$$h(x,t)=\int_\Omega m(y,t)\,g(x-y)\,dy,$$

and the movement model with nonlocal information gathering and attraction strength $\gamma>0$ is

$$\partial_tu=d\,\partial_{xx}u-\gamma\,\partial_x\big(u\,\partial_xh\big),\qquad \int_\Omega u(x,t)\,dx=1,$$

with the conservation enforced by no-flux boundary conditions. For a general potential $a(x,t)$ the perceived potential is $a_{g,R}=\int_\Omega a(y,t)g(x-y)\,dy$, and $u$ drifts up its gradient.

## Depends on

This node has no prerequisites.

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Expansion

Movement models of this form arise from a master equation $u(x,t+\tau)=\int f(x,y,t;\tau)u(y,t)\,dy$ for a redistribution kernel $f$; Taylor expansion in the jump and the limit $\tau\to0^+$ give the Fokker–Planck equation $\partial_tu=-\nabla\cdot(cu)+\sum_{i,j}\partial_{ij}(d_{ij}u)$, with drift $c$ and diffusion $d_{ij}$ equal to the first and half the second moments of the jump per unit time. Biasing jumps up the perceived gradient gives the advection term. As $R\to0^+$, $h\to m$ and the model becomes the local taxis equation $\partial_tu=d\,\partial_{xx}u-\gamma\,\partial_x(u\,\partial_xm)$. For a prescribed resource the equation is linear in $u$; for a constant resource on a periodic domain $\partial_xh=0$ and it is the heat equation for every $R$, so no instability arises. The destabilisation of homogeneous states as $R$ decreases, and the ill-posedness of the local limit at high wavenumbers, which the review discusses in Section 5.2.1, belong to interacting-population systems in which the perceived density is that of a population rather than a prescribed resource.

## Sources

- H. Wang, Y. Salmaniw, "Open problems in PDE models for knowledge-based animal movement via nonlocal perception and cognitive mapping", J. Math. Biol. (2023), Section 2.1, Equations (2.2)–(2.5), Section 3.1, Equations (3.1)–(3.7), Section 5.2.1, <https://doi.org/10.1007/s00285-023-01905-9>.
