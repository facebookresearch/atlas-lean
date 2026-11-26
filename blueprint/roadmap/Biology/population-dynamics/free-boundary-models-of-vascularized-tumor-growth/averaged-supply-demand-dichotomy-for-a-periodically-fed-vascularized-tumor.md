# Averaged supply–demand dichotomy for a periodically fed vascularized tumor

**Model.** A planar tumor occupies a domain $\Omega(t)\subset\mathbb R^2$. After nondimensionalization, the quasi-steady nutrient $u$, the pressure $p$ and the free boundary satisfy
$$\Delta u-u=0\ \text{in }\Omega(t),\qquad \partial_nu+\alpha\big(u-\phi(t)\big)=0\ \text{on }\partial\Omega(t),$$
$$-\Delta p=\mu\big(u-\psi(t)\big)\ \text{in }\Omega(t),\qquad p=\kappa\ \text{on }\partial\Omega(t),\qquad V_n=-\partial_np\ \text{on }\partial\Omega(t),$$
where $\kappa$ is the boundary curvature (cell–cell adhesion), $\alpha>0$ the vascular (Robin) exchange coefficient, $\mu>0$ the tumor aggressiveness, Darcy's law gives the cell velocity $-\nabla p$, and $\phi(t)>0$ (nutrient supply) and $\psi(t)>0$ (nutrient demand, the proliferation threshold) are continuous $T$-periodic functions with means $\bar\phi,\bar\psi$.

**Radial reduction.** For a disk $\Omega(t)=B_{R(t)}$ the nutrient is $u=\dfrac{\alpha\phi(t)\,I_0(r)}{I_1(R)+\alpha I_0(R)}$ (modified Bessel functions), and integrating the pressure equation gives
$$R'=\mu R\Big(f_0(R)\phi(t)-\tfrac12\psi(t)\Big),\qquad f_0(r)=\frac{\alpha I_1(r)}{r\big(I_1(r)+\alpha I_0(r)\big)},$$
where $f_0$ decreases strictly from $f_0(0^+)=\frac12$ to $f_0(+\infty)=0$. For every $R(0)>0$ this ODE has a unique global $C^1$ solution with $R(t)>0$.

**Theorem.**
1. If $\bar\phi\le\bar\psi$, the tumor vanishes: $R(t)\to 0$.
2. If $\bar\phi>\bar\psi$, there is a unique positive $T$-periodic radius $R_\ast(t)$, and it is globally attracting among positive solutions: $|R(t)-R_\ast(t)|\to 0$ for every $R(0)>0$.

Thus the long-time fate is decided by the time averages alone, and a persistent tumor synchronizes with the nutrient cycle.

## Expansion

Write $R'=\mu R\,G(t,R)$ with $G$ strictly decreasing in $R$ because $f_0$ is. Since $f_0<\frac12$, $(\ln R)'<\frac{\mu}{2}(\phi-\psi)$, and integrating over periods drives $\ln R$ to $-\infty$ when $\bar\phi<\bar\psi$; the boundary case $\bar\phi=\bar\psi$ needs a finer argument using strict monotonicity of $f_0$. When $\bar\phi>\bar\psi$, small radii grow over one period because $f_0(0^+)=\frac12$, and large radii shrink because $f_0\to 0$, so the period map $r\mapsto R(T;0,r)$ maps an interval into itself and has a fixed point. Strict monotonicity of $G$ in $R$ rules out two ordered periodic solutions, giving uniqueness, and comparison with $R_\ast$ from above and below gives global attraction.

## Sources

- Xinyue Zhao, "A free-boundary model of vascularized tumor growth with time-periodic coefficients", arXiv:2606.11501 (2026), Theorem 1.1 and Section 2: Lemma 2.1 and Theorems 2.2–2.5, <https://doi.org/10.48550/arXiv.2606.11501>.
