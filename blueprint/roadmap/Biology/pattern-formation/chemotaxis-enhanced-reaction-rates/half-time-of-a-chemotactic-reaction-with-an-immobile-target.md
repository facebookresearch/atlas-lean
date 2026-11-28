# Half-time of a chemotactic reaction with an immobile target

**Model.** A mobile species $\rho_1$ (sperm, monocytes, pollinators) diffuses in $\mathbb{R}^2$ and is chemotactically attracted to an immobile target density $\rho_2$ (egg, inflamed tissue, flower) that secretes a fast-diffusing attractant; the two react on contact. After rescaling,

$$\partial_t\rho_1-\Delta\rho_1+\chi\nabla\cdot\big(\rho_1\nabla(-\Delta)^{-1}\rho_2\big)=-\epsilon\rho_1\rho_2,\qquad \partial_t\rho_2=-\epsilon\rho_1\rho_2 .$$

The target starts as $\rho_2(x,0)=\theta\eta(x)$ with radial smooth $\eta$, $\mathbf 1_{B_1}\le\eta\le1$, and the mobile species starts at distance $\sim L$: $\int_{|x|\le L}\rho_1(x,0)\,dx\ge M_0$ while $\int_{|x|\le1}\rho_1(x,0)\,dx\ll M_0$. Set $\gamma=\theta\chi$ (attraction strength). The *half-time* $\tau$ is the time at which the mass of $\rho_2$ has decreased by $\pi\theta/2$.

**Theorem.** Assume both initial densities are radially symmetric and $\chi\gamma/\epsilon\ge c>0$. There is $B>0$ depending only on $c$ such that, if

$$\frac{M_0\epsilon}{\gamma}\ge B,\qquad \gamma\ge B,\qquad \frac{M_0}{\theta}\ge B ,$$

then the chemotactic half-time satisfies

$$\tau_C\lesssim\frac{L^2}{\gamma}+\log\gamma .$$

In contrast, without chemotaxis ($\chi=0$) and with $\rho_1(\cdot,0)$ supported in $\{|x|\ge L/2\}$, the pure reaction–diffusion half-time obeys

$$\tau_D\gtrsim\frac{L^2}{\log(\epsilon M_0)} .$$

So for strong attraction ($\gamma\gg\log(\epsilon M_0)$) chemotaxis shortens the time to react by a factor of order $\gamma/\log(\epsilon M_0)$. A quarter of the target mass in fact reacts by time $C_1L^2/\gamma$ in the regime where the transport bound dominates.

## Expansion

*Linear comparison.* While at least half the target mass remains, $\rho_2(\cdot,t)$ is more concentrated (in the sense of radial mass functions) than $g=\theta(\mathbf 1_{B_1}-\mathbf 1_{B_{1/\sqrt2}})$, so by a mass comparison principle for radial Fokker–Planck equations $\rho_1$ is at least as concentrated as the solution of the linear equation $\partial_t\rho-\Delta\rho+\nabla\cdot(\rho\nabla H)=0$ with the explicit potential $H=\chi(-\Delta)^{-1}g$, which equals $-(\gamma/4)\log r$ for $r\ge1$, up to an error of half the target mass.

*Transport.* For the linear problem, a comparison argument for the dual equation shows that radial data initially near $r\le L$ deliver a fixed fraction $cM_0$ of mass to $B_{6/7}$ by time $C_1L^2/\gamma$: the drift $|\nabla H|\sim\gamma/r$ moves mass inward ballistically on the diffusive scale. The weak weighted Poincaré inequality controls the subsequent relaxation to the ground state, which costs the $\log\gamma$ term.

*Reaction.* Once $\rho_1$ sits near the target, a parabolic Harnack ("pass-through") estimate gives $\int_0^{t_3+1}\rho_1(r,t)\,dt\ge cM_0/\gamma$ for $r\in(1/2,1)$, which with $\epsilon M_0\gg\gamma$ eats half the target. Without chemotaxis, mass must arrive by diffusion alone, and a heat-kernel bound gives the lower estimate for $\tau_D$. The authors note that the unbounded Keller–Segel flux may overstate the gain and suggest flux-limited chemotaxis as a better model.

## Depends on

- [Weak weighted Poincaré inequality for logarithmic potentials](weak-weighted-poincare-inequality-for-logarithmic-potentials.md)
- [$L^\infty$ bound for Fokker–Planck equations with a semiconvex drift potential](linfty-bound-for-fokker-planck-equations-with-semiconvex-drift-potential.md)

## Sources

- Alexander Kiselev, Fedor Nazarov, Lenya Ryzhik, Yao Yao, "Chemotaxis and Reactions in Biology", arXiv:2004.06441 (2020): Theorem 1.1 (half-time bounds), Proposition 4.2 and Proposition 4.3 (mass comparison), Theorem 7.1, Corollary 7.2 and Theorem 7.3 (transport and quarter-mass reaction time), Proposition 8.1 (pass-through estimate). <https://doi.org/10.48550/arXiv.2004.06441>. Published version: Journal of the European Mathematical Society 25(7) (2022), 2641–2696, <https://doi.org/10.4171/jems/1247>; locators above refer to the arXiv version.
