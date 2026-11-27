# Outer solution and shock location for motor density on a microtubule

**Mean-field model.** On a microtubule $[0, \ell]$, the mean motor occupancy $\rho_\varepsilon(x) \in [0,1)$ of a totally asymmetric exclusion process with attachment rate $\Omega_A$, detachment rate $\Omega_D$ ($\Omega_A > \Omega_D$), motility $v(x)$ and lattice spacing $\varepsilon$ solves

$$\partial_x\Big[v(x)\Big(-\frac{\varepsilon}{2}\partial_x\rho_\varepsilon + \rho_\varepsilon(1 - \rho_\varepsilon)\Big)\Big] = \Omega_A - (\Omega_A + \Omega_D)\rho_\varepsilon, \qquad \rho_\varepsilon(0) = \alpha, \quad \rho_\varepsilon(\ell) = 1 - \beta,$$

with entry rate $\alpha$ and exit rate $\beta$. The **outer solution** is the pointwise limit $\rho_0 = \lim_{\varepsilon\to 0}\rho_\varepsilon$. For a homogeneous microtubule ($v \equiv v_0$) let $g(x; s, a)$ solve the reduced first-order problem

$$v_0(1 - 2g)\,\partial_x g = \Omega_A - (\Omega_A + \Omega_D) g, \qquad g(s; s, a) = a,$$

taking for $a = 1/2$ the branch with $g > 1/2$ for $x < s$. Starting from $a < 1/2$, the solution reaches density $1/2$ after the distance

$$x_a = v_0\frac{\Omega_A - \Omega_D}{(\Omega_A + \Omega_D)^2}\log\frac{\Omega_A - \Omega_D}{2(\Omega_A - a(\Omega_A + \Omega_D))} + v_0\frac{1 - 2a}{\Omega_A + \Omega_D}.$$

**Theorem (homogeneous microtubule).** The outer solution is

$$\rho_0(x) = \begin{cases} \alpha, & x = 0, \\ g(x; 0, \alpha), & 0 < x < \max\{0, x_J\}, \\ g(x; \ell, \max\{1/2,\ 1 - \beta\}), & \max\{0, x_J\} < x < \ell, \\ 1 - \beta, & x = \ell, \end{cases}$$

where $x_J = 0$ if $\alpha \ge 1/2$, and otherwise $x_J = \min\{x \ge 0 : g(x; 0, \alpha) + g(x; \ell, \max\{1/2, 1 - \beta\}) \le 1\}$ is the position of the shock (traffic jam). If $\alpha \ge 1/2$ or $\int_0^{1/2}\frac{v_0(1 - 2\rho)}{\Omega_A - (\Omega_A + \Omega_D)\rho}\, d\rho \le \ell$, then $\rho_0(\ell^-) = \max\{1/2, 1 - \beta\}$, and $\rho_0$ is continuous at $\ell$ when $\beta < 1/2$; otherwise a boundary layer forms at the exit.

**Defective region.** If the motility jumps at $x_0$ from $v_L$ to $v_R$ (with continuity of density and flux imposed at $x_0$ in the $\varepsilon$-problem), the outer solution is again built from the reduced solutions $g_L$, $g_R$ on each side. When $v_L > v_R$ (motors slow down entering the defect) $\rho_0$ has a jump at $x_0$, so a jam forms at the defect; when $v_R > v_L$ the outer solution is given by an analogous explicit formula involving $g_R(x_0; 1, \max\{1/2, 1 - \beta\})$.

## Expansion

Letting $\varepsilon \to 0$ removes the diffusion term, leaving a first-order equation that cannot meet both boundary values. Integrating the equation shows the flux $J = v\rho(1 - \rho) - \tfrac{\varepsilon v}{2}\rho'$ changes by $\int(\Omega_A - (\Omega_A + \Omega_D)\rho)$, so in the limit the left branch carries the entry condition and the right branch the exit condition. They are glued by an internal layer (a viscous shock of Burgers type) where the two branches have equal flux $\rho(1 - \rho)$, i.e. $g_{\mathrm{left}} + g_{\mathrm{right}} = 1$, which defines $x_J$. Boundary layers near the ends absorb mismatches, and the limit density at the exit saturates at $1/2$ (maximal current) when $\beta > 1/2$. At a motility drop, flux continuity with a smaller $v$ forces a density jump, which Monte Carlo simulations of the exclusion process confirm as motor accumulation at defective regions.

## Sources

- S. D. Ryan, Z. McCarthy, M. Potomkin, "Motor Protein Transport Along Inhomogeneous Microtubules", Bulletin of Mathematical Biology 83 (2021), 9, <https://doi.org/10.1007/s11538-020-00838-4>. Published version of arXiv:2005.01955, cited next; locators there refer to the arXiv version.
- Shawn D. Ryan, Zachary McCarthy, Mykhailo Potomkin, "Motor protein transport along inhomogeneous microtubules", arXiv (2020). Section 2, Theorem 1, Corollary 1, Theorems 2 and 3, Appendix A. <https://doi.org/10.48550/arXiv.2005.01955>
