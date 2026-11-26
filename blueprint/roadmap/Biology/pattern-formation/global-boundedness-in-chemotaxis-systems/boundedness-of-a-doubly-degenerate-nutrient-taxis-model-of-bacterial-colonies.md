# Boundedness of a doubly degenerate nutrient-taxis model of bacterial colonies

Bacterial colonies such as *Bacillus subtilis* on nutrient-poor agar are modeled, with nutrient taxis, by

$$u_t=\nabla\cdot(uv\nabla u)-\chi\nabla\cdot(u^{\alpha}v\nabla v)+\ell uv,\qquad v_t=\Delta v-uv,$$

in a smooth bounded convex domain $\Omega\subset\mathbb R^n$ with no-flux boundary conditions, where $u$ is bacterial density, $v$ nutrient concentration, $\chi>0$, $\ell\ge0$, $\alpha\ge1$. The cell diffusion degenerates both at $u=0$ (porous-medium type) and at $v=0$ (cross-degeneracy).

**Theorem.** Let $n\in\{3,4,5\}$ and

$$1\le\alpha<\frac52-\frac n4 .$$

For any $u_0\in W^{1,\infty}(\Omega)$ nonnegative, $u_0\not\equiv0$, and $v_0\in W^{1,\infty}(\Omega)$ positive on $\overline\Omega$, there is a global weak solution with $u\ge0$, $v>0$, $u,v$ continuous on $\overline\Omega\times[0,\infty)$, and

$$\sup_{t>0}\big(\|u(t)\|_{L^\infty}+\|v(t)\|_{W^{1,\infty}}\big)<\infty .$$

Moreover there is $u_\infty\in C^0(\overline\Omega)$ with $u(t)\to u_\infty$ and $v(t)\to0$ in $L^\infty(\Omega)$ as $t\to\infty$. The limit $u_\infty$ is generally non-constant: it equals $w(\cdot,1)$ for a weak solution $w$ of a time-rescaled degenerate parabolic problem $w_\tau=\nabla\cdot(a\,w\nabla w)-\nabla\cdot(b\,w^{\alpha})+\ell a w$ on $\tau\in(0,1)$, whose coefficients satisfy $C^{-1}\le a\le C$, $|b|\le C$.

For $n=3$ this covers all $\alpha\in[1,7/4)$, and gives the first global boundedness results for $n=4,5$.

## Expansion

The functional $\int u\ln u+a\int|\nabla v|^4/v^3$ stays bounded for $\alpha<\frac32+\frac1n$, giving the space–time bound $\int_0^\infty\int u|\nabla v|^4/v^3+v|\nabla u|^2\le C$. A bootstrap based on a refined functional inequality upgrades this to a uniform $L^{p_0}$ bound with $p_0=\frac{2n(2-\alpha)}{n-2}$, and $p_0>n/2$ exactly when $\alpha<\frac52-\frac n4$. Energy estimates then give all $L^p$ bounds and Moser iteration gives $L^\infty$. Since nutrients are only consumed, $\int_0^\infty\|v\|_{L^\infty}<\infty$; a pointwise Harnack inequality for $v$ lets one change time to $\tau=\phi(t)\in(0,1)$, turning the $u$-equation into a uniformly parabolic-in-$v$ degenerate equation whose endpoint is the frozen pattern $u_\infty$. Biologically, the colony grows by consuming the nutrient and freezes into a final spatial pattern once nutrient is exhausted.

## Sources

- M. Le, *$L^\infty$ bounds and asymptotic behavior in a doubly degenerate chemotaxis system below six dimensions* (2026), Theorem 1.1 (global existence and uniform boundedness) and Theorem 1.2 (large-time behavior). <https://doi.org/10.48550/arXiv.2607.27949>
