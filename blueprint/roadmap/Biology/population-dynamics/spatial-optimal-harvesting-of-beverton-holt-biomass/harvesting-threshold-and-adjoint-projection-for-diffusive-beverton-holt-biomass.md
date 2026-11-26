# Harvesting threshold and adjoint projection rule for a diffusive Beverton–Holt biomass model

**Model.** Fish biomass $B(x,t)\ge0$ on a bounded domain $\Omega$ with no-flux boundary satisfies

$$\partial_tB=D\Delta B+\frac{aB}{b+B}-\alpha u(x,t)B-mB,$$

with Beverton–Holt production $aB/(b+B)$ ($a,b>0$), natural mortality $m>0$, catchability $\alpha>0$ and harvesting effort $0\le u\le u_{\max}$.

**Proposition (well-posedness).** For $0\le B_0\in L^\infty(\Omega)$ and measurable admissible $u$, there is a unique global mild solution $B\in C([0,T];L^2)\cap L^2(0,T;H^1)$, classical for $t>0$ under regularity of $B_0$ and $\partial\Omega$, with $0\le B\le\|B_0\|_\infty+aT$. In the spatially homogeneous (ODE) model the sharper bound $0\le B(t)\le\max\{B_0,a/m\}$ holds.

**Proposition (recovery threshold).** For constant effort $u\equiv u_c$ the equilibria are $B_0^*=0$ and

$$B_1^*(u_c)=\frac{a}{m+\alpha u_c}-b,$$

which is positive if and only if

$$u_c<u_{\mathrm{crit}}:=\frac1\alpha\Big(\frac ab-m\Big).$$

When it exists, the positive homogeneous equilibrium is linearly asymptotically stable under Neumann conditions, and the extinction state is linearly asymptotically stable when $u_c>u_{\mathrm{crit}}$.

**Theorem (optimal distributed harvesting).** For $\gamma>0$, the problem of maximizing

$$J(u)=\int_0^T\!\!\int_\Omega\Big(\alpha uB-\frac\gamma2u^2\Big)\,dx\,dt$$

over admissible efforts has an optimal control $u^*$. With the adjoint $p$ solving

$$-\partial_tp-D\Delta p=\frac{ab}{(b+B^*)^2}\,p-mp+\alpha u^*(1-p),\qquad p(\cdot,T)=0,\quad\partial_\nu p=0,$$

the optimal effort is given pointwise by the projection

$$u^*(x,t)=\min\Big\{u_{\max},\max\Big\{0,\frac{\alpha B^*(x,t)\,\big(1-p(x,t)\big)}{\gamma}\Big\}\Big\}.$$

The adjoint $p$ is the marginal future value of a unit of biomass; harvesting is reduced where $p$ is close to $1$, i.e. where standing stock is worth more left in the water than landed.

## Expansion

The threshold follows from linearizing at $B=0$: the per-capita growth rate there is $a/b-m-\alpha u_c$, so extinction is stable exactly when effort exceeds $u_{\mathrm{crit}}$; at the positive equilibrium the derivative of the Beverton–Holt term, $ab/(b+B^*)^2$, is below the per-capita loss $m+\alpha u_c$, which with the nonpositive Neumann Laplacian spectrum gives stability of every spatial mode. The optimality system comes from the Hamiltonian $\mathcal H=\alpha uB-\frac\gamma2u^2+p\,(\text{reaction terms})$: $\partial_u\mathcal H=\alpha B(1-p)-\gamma u$, and the quadratic cost makes the maximizer unique, so the box constraint is enforced by projection.

## Sources

- Tin Nwe Aye, Wolfgang Bock, "Spatially Explicit Optimal Harvesting and Adjoint-Based Diagnostics for Nonlinear Biomass Dynamics", arXiv:2610.08374 (2026): Propositions 1–2 (reduced model), Theorems 3–4, Proposition 5, Theorem 6 and Section 7.1 (adjoint equation and projection formula). <https://doi.org/10.48550/arXiv.2610.08374>
