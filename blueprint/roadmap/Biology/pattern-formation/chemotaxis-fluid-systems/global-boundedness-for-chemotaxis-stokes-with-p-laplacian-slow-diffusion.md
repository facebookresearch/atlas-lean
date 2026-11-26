# Global boundedness for three-dimensional chemotaxis–Stokes with $p$-Laplacian slow diffusion

Let $\Omega\subset\mathbb R^3$ be a bounded smooth domain. Consider bacteria of density $n$ consuming oxygen $c$ in an incompressible Stokes fluid with velocity $u$ and pressure $\pi$:
$$\begin{cases}
n_t+u\cdot\nabla n=\nabla\cdot\big(|\nabla n|^{p-2}\nabla n\big)-\chi\nabla\cdot(n\nabla c),\\
c_t+u\cdot\nabla c-\Delta c=-cn,\\
u_t+\nabla\pi=\Delta u+n\nabla\phi,\qquad\operatorname{div}u=0,
\end{cases}\qquad x\in\Omega,\ t>0,$$
with no-flux conditions $(|\nabla n|^{p-2}\nabla n-\chi n\nabla c)\cdot\nu=\partial_\nu c=0$ and $u=0$ on $\partial\Omega$. Here $\chi>0$ and $\phi$ is a gravitational potential. Assume $n_0\in L^\infty(\Omega)$ with $\nabla n_0^{1-1/p}\in L^p(\Omega)$, $c_0\in W^{2,r}(\Omega)$ and $u_0\in W^{2,r}(\Omega)\cap W^{1,r}_0(\Omega)$ with $\operatorname{div}u_0=0$ for all $r>1$, $\phi\in W^{1,\infty}(\Omega)$, and $n_0,c_0\ge0$.

**Theorem.** For every $p>2$ the problem has a global bounded strong solution $(n,c,u,\pi)$, with no logistic damping and no smallness condition on the data. For every $\beta\in(\tfrac34,1)$ and $r>1$,
$$\sup_{t>0}\Big(\|n\|_{L^\infty}+\|c\|_{W^{1,\infty}}+\|u\|_{W^{1,\infty}}+\|\nabla n\|_{L^p}+\|A^\beta u\|_{L^2}\Big)\le M_1(\beta),$$
where $A$ is the Stokes operator. On unit time cylinders $Q_1(t)=\Omega\times(t,t+1)$, the quantities $n_t$, $\Delta_pn$, $|\nabla n|^{p-2}D^2n$ (in $L^2$), $\nabla n$ (in $L^{2p}$), $(c,u)$ (in $W^{2,1}_r$) and $\nabla\pi$ (in $L^r$) are bounded uniformly in $t$.

## Expansion

Earlier results gave global boundedness only for $p>p^*\approx2.01247$, the root of an explicit polynomial condition in $(2,\sqrt{13/3})$. Moser-type $L^q$ iterations saturate as $p\searrow2$, because the extra regularity from the degenerate diffusion vanishes in that limit. This proof instead uses a weighted second-order energy for regularized solutions: it bounds $\int_\Omega(|\nabla n_\varepsilon|^2+\varepsilon)^{p/2}/\rho+|\nabla c_\varepsilon|^4+|\Delta c_\varepsilon|^2$ uniformly in $\varepsilon$ and time, together with space-time integrals of $(|\nabla n_\varepsilon|^2+\varepsilon)^{p-2}|D^2n_\varepsilon|^2/\rho$. The weight $\rho$ is built from the signal, and a weighted Rellich identity supplies the second-order coercivity of the $p$-Laplacian. Signal consumption gives $\|c\|_\infty\le\|c_0\|_\infty$ and an energy for $\int|\nabla c|^4/c^3$-type quantities. These estimates hold for all $2<p\le3$, cover the remaining near-linear range $(2,p^*]$, and complete the boundedness theory for $p>2$.

## Sources

- Chunhua Jin, "Chemotaxis-Stokes system with $p$-Laplacian slow diffusion: global boundedness across the full $p>2$ range", arXiv:2611.01847 (2026), Section 2 (system, Assumption 2.1 on the data, Theorem 2.1) and Proposition 4.1 (key a priori estimate), <https://doi.org/10.48550/arXiv.2611.01847>.
