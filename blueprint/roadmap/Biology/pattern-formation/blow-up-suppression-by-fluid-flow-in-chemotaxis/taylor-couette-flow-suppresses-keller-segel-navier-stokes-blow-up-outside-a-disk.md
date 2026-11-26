# Taylor-Couette flow suppresses Keller-Segel-Navier-Stokes blow-up outside a disk

**Model.** Cells of density $n$ in a fluid with velocity $v$ and pressure $P$, in the exterior of the unit disk $\Omega = \{x\in\mathbb{R}^2 : |x| > 1\}$, $r = |x|$, follow the Patlak-Keller-Segel-Navier-Stokes system

$$\partial_t n + v\cdot\nabla n = \Delta n - \nabla\cdot(n\nabla c), \qquad -\Delta c + c = n, \qquad \partial_t v + v\cdot\nabla v + \nabla P = \Delta v + n\nabla r, \qquad \nabla\cdot v = 0,$$

with buoyancy-type forcing $n\nabla r$. For $A \ge 1$, the Taylor-Couette flow $U_A = A(r + r^{-1})e_\theta$ with its radial pressure is a steady solution with $n = c = 0$; write $v = U_A + u$, with initial perturbation $u_{\mathrm{in}}$ and vorticity $w_{\mathrm{in}} = \operatorname{curl}u_{\mathrm{in}}$. Boundary conditions on $r = 1$: $n = c = 0$, $u\cdot e_r = 0$, $w = 0$.

**Theorem.** Let $0 \le n_{\mathrm{in}} \in L^1\cap L^\infty\cap H^1_0(\Omega)$, $u_{\mathrm{in}} \in H^2$ divergence-free with $u_{\mathrm{in}}\cdot e_r = w_{\mathrm{in}} = 0$ on $r = 1$, and $r^2n_{\mathrm{in}}, r^2w_{\mathrm{in}} \in L^2(\Omega)$. No smallness is assumed on the cell mass or on $u_{\mathrm{in}}$.
1. (Global existence) There are $A_0 \ge 1$ and $M_0 > 0$, depending only on $\Omega$ and the initial data, such that for every $A \ge A_0$ there is a unique global strong solution, with
$$\sup_{t\ge0}\big(\|n(t)\|_{L^2} + \|n(t)\|_{L^\infty} + \|c(t)\|_{W^{1,\infty}}\big) \le M_0.$$
2. (Averaging) Let $(N,C)$ be the global radial solution of the Keller-Segel system on $r > 1$ with $N(t,1) = C(t,1) = 0$ and initial density the angular average $N(0,r) = \frac{1}{2\pi}\int_0^{2\pi}n_{\mathrm{in}}(r,\theta)\,d\theta$. Then for all $0 < \delta < T < \infty$,
$$\lim_{A\to\infty}\sup_{\delta\le t\le T}\|n^A(t) - N(t)\|_{L^2(\Omega)} = 0.$$

## Expansion

In coordinates rotating with the flow, the density and vorticity are transported by the angular shear $Ar^{-2}\partial_\theta$, which damps non-radial modes fast (enhanced dissipation), so for large $A$ the density is close to its angular average, which obeys the radial Keller-Segel problem. With the absorbing boundary $r = 1$ the radial solution decays, so the full density becomes small in $L^2$ at some finite time, and a small-data energy estimate then continues it globally. The difficulty specific to the exterior domain is that the shear $Ar^{-2}$ vanishes as $r\to\infty$; radially weighted energy estimates (using the $r^2$-moment assumptions) control density and vorticity at large radii. Shear devices of this type are used to control mixing in cell culture and enzymatic reactors.

## Sources

- Lili Wang, "Blow-up suppression for the Patlak--Keller--Segel--Navier--Stokes system by Taylor--Couette flow outside a disk", arXiv:2611.25442 (2026), Section 1, Theorem 1.1 and Proposition 1.1, <https://doi.org/10.48550/arXiv.2611.25442>.
