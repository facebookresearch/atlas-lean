# Global strong solutions of planar Keller–Segel–Navier–Stokes with mass at most 8π

**System.** On $\mathbb R^2\times(0,T)$ let $n\ge0$ be the cell density, $c$ the chemoattractant concentration, $u$ the fluid velocity, $\pi$ the pressure and $\phi$ a given gravitational potential:

$$
\begin{aligned}
\partial_tn+u\cdot\nabla n&=\Delta n-\nabla\cdot(n\nabla c), & \Delta c+n&=0,\\
\partial_tu+u\cdot\nabla u+\nabla\pi&=\Delta u+n\nabla\phi, & \nabla\cdot u&=0,
\end{aligned}
$$

with $(n,u)|_{t=0}=(n_{in},u_{in})$. The mass $M=\int_{\mathbb R^2}n\,dx$ is conserved. Without the fluid, solutions with $M>8\pi$ (and finite second moment) blow up in finite time, so $8\pi$ is the critical mass.

**Theorem (Theorem 1.1).** Let $\phi\in L^\infty\bigl([0,\infty);\dot W^{1,\infty}(\mathbb R^2)\bigr)$, $0\le n_{in}\in L^1\cap L^\infty(\mathbb R^2)$ and $u_{in}\in W^{1,2}(\mathbb R^2)$. If $\int_{\mathbb R^2}n_{in}\,dx\le8\pi$, there is a global strong solution $(n,u,\pi)$, with no smallness assumption on the velocity and no moment or entropy condition on $n_{in}$.

**Theorem (a priori bound with drift, Theorem 1.2).** Let $0\le n_{in}\in L^1\cap L^\infty(\mathbb R^2)$ with mass $M\le8\pi$ and let $u\in L^\infty\bigl([0,T];W^{1,2}(\mathbb R^2)\bigr)$ be any given divergence-free drift. Then the Keller–Segel equation with drift, $\partial_tn+u\cdot\nabla n=\Delta n-\nabla\cdot(n\nabla c)$, $\Delta c+n=0$, has a global strong solution on $[0,T]$ with

$$
\|n(t)\|_{L^\infty}\le\frac{8\pi}{8\pi-M}\,\|n_{in}\|_{L^\infty}\quad(M<8\pi),\qquad \|n(t)\|_{L^\infty}\le8\|n_{in}\|_{L^\infty}\bigl(1+4T\|n_{in}\|_{L^\infty}\bigr)\quad(M=8\pi),
$$

for $0<t<T$.

## Expansion

Let $n^*(\cdot,t)$ be the decreasing rearrangement of $n(\cdot,t)$ as a function of the area variable $s$ and $k(s,t)=\int_0^sn^*(\tau,t)\,d\tau$ the mass carried by the densest region of area $s$. Because a divergence-free drift preserves the distribution function of $n$, the velocity drops out and $k$ satisfies the differential inequality

$$
\partial_tk-4\pi s\,\partial_s^2k-k\,\partial_sk\le0 ,
$$

which is the same as for the fluid-free Keller–Segel equation. An improved maximum principle comparing $k$ with a suitable auxiliary supersolution then bounds $\partial_sk(0,t)=\|n(t)\|_{L^\infty}$, giving the stated estimates; with $L^\infty$ control of $n$, the forcing $n\nabla\phi$ is bounded in $L^2$ and two-dimensional Navier–Stokes theory yields global $W^{1,2}$ bounds for $u$, closing the argument together with local well-posedness. The threshold is sharp because the fluid-free case ($u\equiv0$) blows up above $8\pi$.

## Sources

- W. Wang, D. Wei and Z. Zhang, "Critical mass threshold for the 2D Patlak–Keller–Segel–Navier–Stokes system", arXiv:2606.02070 (2026), Section 1 (Theorems 1.1–1.2 and the rearrangement inequality), Sections 2–5 (proofs, monotonicity property and improved maximum principle), <https://doi.org/10.48550/arXiv.2606.02070>.
