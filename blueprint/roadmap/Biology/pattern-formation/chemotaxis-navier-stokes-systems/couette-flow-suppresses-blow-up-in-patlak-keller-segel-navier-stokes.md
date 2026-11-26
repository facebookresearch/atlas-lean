# Couette flow suppresses blow-up in the Patlak–Keller–Segel–Navier–Stokes system

**Model.** On $\mathbb T\times\mathbb R$ consider the parabolic–parabolic Patlak–Keller–Segel system for a cell density $n$ and a chemical $c$, transported by an incompressible Navier–Stokes flow $u$ that is buoyancy driven by the cells and perturbs the Couette flow $(Ay,0)$ with amplitude $A>0$:

$$\partial_t n+(Ay,0)\cdot\nabla n+u\cdot\nabla n-\Delta n=-\nabla\cdot(n\nabla c),\qquad \partial_t c+(Ay,0)\cdot\nabla c+u\cdot\nabla c-\Delta c=n-c,$$

$$\partial_t u+(Ay,0)\cdot\nabla u+(Au_2,0)^{\top}+u\cdot\nabla u-\Delta u+\nabla p=(0,n)^{\top},\qquad\nabla\cdot u=0.$$

Without the flow, the two-dimensional Patlak–Keller–Segel system blows up in finite time for large mass.

**Theorem.** Let $0\le n_{\rm in}\in L^1\cap H^2$, $0\le c_{\rm in}\in H^2\cap W^{1,\infty}$ and $u_{\rm in}\in H^3$ with $\nabla\cdot u_{\rm in}=0$, and put $M=\|n_{\rm in}\|_{L^1}$. There is $\bar A>0$, depending only on $M$, $\|n_{\rm in}\|_{H^2}$, $\|c_{\rm in}\|_{H^2}$ and $\|u_{\rm in}\|_{H^3}$, such that for every $A\ge\bar A$ the local strong solution is global and

$$\sup_{t\ge0}\Bigl(\|n(t)\|_{L^\infty}+\|c(t)\|_{W^{1,\infty}}+\|u(t)\|_{L^\infty}\Bigr)\le C\bigl(A,M,\|n_{\rm in}\|_{H^2},\|c_{\rm in}\|_{H^2},\|c_{\rm in}\|_{W^{1,\infty}},\|u_{\rm in}\|_{H^3}\bigr).$$

No smallness is required of the initial chemical gradient or of the mass.

## Expansion

After rescaling time by $A$, the shear $y\partial_x$ mixes the nonzero $x$-modes, which then dissipate on the enhanced time scale $A^{1/3}$ instead of $A$. The proof splits time at $T^*=A^{1/3+\delta}$: on $[0,T^*]$ an energy bound for the nonzero modes holds once $A$ exceeds an explicit threshold growing like $\exp(C\|c_{\rm in}\|_{H^2}^2)$; after $T^*$ the nonzero modes are small, and the $x$-averaged density solves an essentially one-dimensional Keller–Segel equation, which cannot blow up. Space–time estimates in Kelvin-transformed coordinates handle the buoyancy coupling between $n$ and the vorticity.

## Sources

- Xiaomeng Chen, Shikun Cui, Wendong Wang and Yi Zhang, "Blow-up suppression for the 2D parabolic-parabolic Patlak-Keller-Segel-Navier-Stokes system", arXiv:2610.41507 (2026), Theorem 1.1, Propositions 2.1 and 2.2, <https://doi.org/10.48550/arXiv.2610.41507>.
