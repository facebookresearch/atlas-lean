# Degenerate Keller–Segel system with volume filling

**System.** On a bounded domain $\Omega$ with no-flux boundary conditions, for $m\ge1$, $\chi>0$, $\tau,\eta>0$,
$$\partial_t\rho=\operatorname{div}\bigl((1-\rho)\rho^{m-1}\nabla\rho-\chi\rho(1-\rho)\nabla c\bigr),\qquad \tau\,\partial_t c=\eta\Delta c-c+\rho,$$
where $\rho\in[0,1]$ is the cell volume fraction and $c$ the chemoattractant. Diffusion degenerates at $\rho=0$ (porous-medium type, $m>1$) and both diffusion and drift vanish at the packing limit $\rho=1$.

**Theorems.**
1. *(Existence.)* For $m\ge1$ there is a global weak solution with $0\le\rho,c\le1$, $f(\rho)=\rho^m/m-\rho^{m+1}/(m+1)\in L^2(0,T;H^1)$, $c\in L^\infty(0,T;H^1)$ and $\partial_tc,\Delta c\in L^2$.
2. *(Weak–strong uniqueness.)* For $1<m\le2$, a weak solution coincides with any strong solution that stays in $[\kappa,1-\kappa]$, has bounded gradients and satisfies the entropy equality.
3. *(Exponential decay.)* For $1<m\le2$, $\chi\le1$, $|\Omega|=1$ and mass $M=\int\rho_0=\int c_0$: $\|\rho(t)-M\|_{L^2}+\|c(t)-M\|_{H^1}\le Ce^{-\mu t}$.
4. *(Limits.)* As $\tau\to0$ (for $m>1$), solutions converge to the parabolic–elliptic system with $0=\eta\Delta c-c+\rho$; as $\eta\to0$ (for $1<m\le2$), to the system with $\partial_t c=-c+\rho$.
5. *(Steady states in one dimension.)* For $1<m\le2$, $\chi\le1$, or $m>2$ with $\chi$ small, the only steady state is the constant $(M/|\Omega|,M/|\Omega|)$. For $m>2$ and $0<\chi<1/(m-1)$ there are strictly increasing nonconstant steady states with mass $0<M<1$: pattern formation occurs for strongly degenerate diffusion.

## Expansion

The key a priori estimate is the entropy identity for $\int\bigl(\rho(\log\rho-1)+(1-\rho)(\log(1-\rho)-1)+\tfrac\lambda2\tau c^2\bigr)$, whose dissipation contains $\rho^{m-2}|\nabla\rho|^2$; the logistic-type entropy is natural because the mobility is $\rho(1-\rho)$, and it gives $0\le\rho\le1$. For $m\le2$ the factor $\rho^{m-2}\ge1$ controls the cross term $\chi\nabla c\cdot\nabla\rho$ when $\chi\le1$, which yields uniqueness, convergence to the constant state and the absence of patterns. Steady states in one dimension satisfy a first-order equation obtained by integrating the zero-flux condition, $\rho^{m-2}\rho'=\chi c'$, and nonconstant solutions appear only when $m>2$ makes this relation sufficiently nonlinear.

## Sources

- N. Geltner, A. Jüngel, M. Zhang, "Well-posedness and asymptotic limits for a degenerate Keller-Segel system with volume filling", arXiv:2605.21296 (2026), Section 1 (system), Theorems 1–5, Propositions 8–9, <https://doi.org/10.48550/arXiv.2605.21296>.
