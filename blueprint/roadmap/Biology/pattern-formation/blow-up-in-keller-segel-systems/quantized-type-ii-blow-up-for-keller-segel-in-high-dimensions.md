# Quantized type II blow-up for Keller–Segel in high dimensions

**Model.** For radial solutions of the parabolic–elliptic Keller–Segel system $\partial_t\rho=\Delta\rho-\nabla\cdot(\rho\nabla c)$, $-\Delta c=\rho$ on $\mathbb R^d$, the averaged mass $u(r,t)=r^{-d}\int_0^r\rho(s,t)s^{d-1}\,ds$ satisfies the local scalar equation

$$\partial_t u=\partial_{rr}u+\frac{d+1}{r}\partial_r u+u\,(r\partial_r u+d\,u),$$

with scaling $u_\lambda(r,t)=\lambda^{-2}u(r/\lambda,t/\lambda^2)$. Let $Q$ be the normalized positive stationary state, and let

$$\gamma(d)=\tfrac12\Bigl(d-2-\sqrt{(d-2)(d-10)}\Bigr)\in(2,3]\qquad(d\ge11),$$

the smaller root of $x^2-(d-2)x+2(d-2)=0$. A blow-up at time $T$ is of type II if $(T-t)\|u(t)\|_{L^\infty}$ is unbounded.

**Theorem.** Let $d\ge11$ and fix an integer $l\ge2$ (equivalently $2l>\gamma$). There is a smooth radial solution that blows up at a finite time $T$ with

$$u(t,r)=\frac{1}{\lambda^2(t)}\Bigl[Q\Bigl(\frac{r}{\lambda(t)}\Bigr)+\varepsilon\Bigl(t,\frac{r}{\lambda(t)}\Bigr)\Bigr],\qquad \lambda(t)=c(u_0)\,(T-t)^{l/\gamma}\bigl(1+o(1)\bigr),\quad c(u_0)>0,$$

such that:
1. the regime is stable within a codimension-$(l-1)$ class of radial initial data;
2. $\varepsilon\to0$ in $L^\infty(|y|\le B)$ for every $B>0$;
3. $\|\nabla^\sigma\varepsilon\|_{L^2}\to0$ for every $\sigma\in[d/2+2,\mathfrak s(l)]$, with $\mathfrak s(l)\to\infty$ as $l\to\infty$.

The density stays nonnegative throughout the lifespan. Since $l/\gamma>1/2$, the rate is faster than self-similar, so the blow-up is of type II.

## Expansion

For $d\ge11$ the stationary state decays like $r^{-\gamma}$ and the linearized operator around $Q$ has no positive eigenvalue but a discrete family of resonances. A finite-dimensional system of modulation parameters $b_1,\dots,b_L$ multiplying generalized kernel elements produces approximate profiles; the special solution $b_1\sim c/s$ selected by the $l$-th excited regime gives $\lambda\sim(T-t)^{l/\gamma}$. A bootstrap with high-order weighted energy estimates controls the remainder, and the $l-1$ unstable directions of the parameter ODE are removed by a topological (Brouwer) argument, which is the codimension in item 1. The construction parallels Merle–Raphaël–Rodnianski type II blow-up for supercritical heat and Schrödinger equations.

## Sources

- Thomas Y. Hou, Xiang Qin, Peicong Song and Zirui Wang, "On the Stability of Type II Blowup for the Keller-Segel System in High Dimensions", arXiv:2609.16467 (2026), Theorem 1.1, Section 1.1 and Propositions 2.1–2.2, <https://doi.org/10.48550/arXiv.2609.16467>.
