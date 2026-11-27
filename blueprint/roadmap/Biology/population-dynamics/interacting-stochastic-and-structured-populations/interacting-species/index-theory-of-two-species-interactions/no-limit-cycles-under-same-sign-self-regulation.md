# No limit cycles under same-sign self-regulation

**Setting.** Two species with densities $x,y\ge0$ follow $\dot x=x f(x,y)$, $\dot y=y g(x,y)$ with $f,g$ of class $C^1$ on the open quadrant $\{x>0,y>0\}$; no sign is imposed on the interspecific effects $\partial f/\partial y$, $\partial g/\partial x$.

**Proposition.** If $\partial f/\partial x$ and $\partial g/\partial y$ are both nonpositive everywhere, or both nonnegative everywhere, in the open quadrant, and are not both identically zero there, then the system has no limit cycle in the open quadrant.

## Expansion

Use the Dulac function $B(x,y)=1/(xy)$. Then

$$\frac{\partial}{\partial x}\Big(\frac{xf}{xy}\Big)+\frac{\partial}{\partial y}\Big(\frac{yg}{xy}\Big)=\frac{1}{y}\frac{\partial f}{\partial x}+\frac{1}{x}\frac{\partial g}{\partial y},$$

which has one sign in the open quadrant. If $\gamma$ is a periodic orbit enclosing a region $D$ of the open quadrant, Green's theorem gives $\iint_D \operatorname{div}(BF)\,dx\,dy=0$, so the divergence vanishes identically on $D$. The first-return map on a transversal inside $\gamma$ is then the identity, since the region between an orbit arc and the transversal has zero flux through its sides, so $\gamma$ is a limit of periodic orbits from inside and is not isolated: it is not a limit cycle. Nonconstant periodic orbits are not excluded: if both self-effects vanish on an open set, a center may sit there. For instance $f=1-y-\varphi(x)$, $g=x-1$ with $\varphi$ of class $C^1$, nondecreasing, $\varphi\equiv0$ on $[1/2,3/2]$, $\varphi(x)=(x-3/2)^2$ for $x>3/2$ and $\varphi(x)=-(x-1/2)^2$ for $x<1/2$, satisfies the hypotheses, and on the strip $1/2\le x\le3/2$ it is the Lotka–Volterra system, whose level sets $x-\ln x+y-\ln y=2+\varepsilon$ near $(1,1)$ are periodic orbits. If instead $\partial f/\partial x$ and $\partial g/\partial y$ are not both identically zero on any open subset of the quadrant, the divergence vanishes on no open set and the Bendixson–Dulac criterion excludes every nonconstant periodic orbit. Thus purely competitive self-regulation, or purely positive self-density-dependence in both species, cannot generate isolated oscillations whatever the (possibly density-dependent, mutualistic or parasitic) interspecific terms; mutualistic limit cycles require at least one species whose own density effect changes sign, or opposite-sign self-effects in the two species.

## Sources

- Chloe Mian, Sylvain Billiard, Violaine Llaurens, Charline Smadi, "Dynamics of Two Species with Density-Dependent Interactions and Application to Mutualism", *Bulletin of Mathematical Biology* 88(9) (2026), 152, Proposition 4.8 (Section 4), <https://doi.org/10.1007/s11538-026-01724-1> (preprint arXiv:2509.06062).
