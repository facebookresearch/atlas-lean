# Nonlinear diffusion limit of volume-filling Keller–Segel

**Model.** In a bounded domain $\Omega$ with no-flux conditions, consider the parabolic–elliptic Keller–Segel system with porous-medium diffusion and volume-filling sensitivity $u(1-u)$:
$$\partial_tu-\delta\Delta\frac{u^m}{m}+\nabla\cdot\bigl[\chi u(1-u)\nabla v\bigr]=0,\qquad -D\Delta v+v=u,\qquad 0\le u^0\le1 .$$
The chemotactic flux vanishes at $u=0$ and at the packing density $u=1$, so $0\le u\le1$ is preserved. Let $M$ be the mean of $u^0$.

**Theorem (fast-signal limit).** Let $\delta=1$, $D=\varepsilon^2$, $1\le m<2$ and
$$\chi<\frac{(3-m)^{3-m}}{(2-m)^{2-m}} .$$
For energy solutions $(u_\varepsilon,v_\varepsilon)$ with fixed initial datum satisfying the entropy inequality, along a subsequence $u_\varepsilon\to u$ and $v_\varepsilon\to u$ strongly in $L^p(\Omega\times(0,T))$ for every $p<\infty$, where $u\in L^\infty\cap L^2(0,T;H^1)$ is a weak solution of the scalar equation
$$\partial_tu-\Delta\frac{u^m}{m}+\nabla\cdot\bigl[\chi u(1-u)\nabla u\bigr]=0$$
with no-flux boundary conditions.

**Stationary states and stability.** Under the same threshold (with $\le$), the only stationary state is the constant $u\equiv v\equiv M$. If the strict inequality holds, then for every $1\le p,q<\infty$, $\|u(t)-M\|_{L^p}+\|v(t)-M\|_{L^q}\le Ce^{-ct}$ with $C,c$ independent of $\varepsilon$.

## Expansion

The limiting equation has effective diffusivity $u^{m-1}-\chi u(1-u)$, which is positive on $[0,1]$ exactly when $\chi<\min_{0<u<1}u^{m-2}/(1-u)$; minimizing at $u=(2-m)/(3-m)$ gives the threshold $(3-m)^{3-m}/(2-m)^{2-m}$, equal to $4$ for $m=1$. Below it the limit is forward parabolic. Because the sensitivity is nonlinear in $u$, weak convergence does not identify the flux; the strong compactness of $u_\varepsilon$ comes from the free-energy and entropy dissipation estimates, which are uniform in $\varepsilon$ in this parabolic regime.

## Sources

- Mingyue Zhang, "Three asymptotic regimes for a Keller–Segel system with volume-filling effect", arXiv:2609.04599 (2026), Section 3, Theorem 3, Proposition 5 and Theorem 6, <https://doi.org/10.48550/arXiv.2609.04599>.
