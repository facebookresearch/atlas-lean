# Global boundedness in a chemo-repulsion–haptotaxis system

Let $\Omega\subset\mathbb{R}^n$ ($n\ge2$) be bounded and smooth, $\chi,\xi\ge0$, $\tau\in\{0,1\}$, and consider
$$\begin{cases}
u_t=\Delta u+\chi\nabla\cdot(u\nabla v)-\xi\nabla\cdot(S(u)\nabla w), & x\in\Omega,\ t>0,\\
\tau v_t=\Delta v-v+u,\\
w_t=-vw,
\end{cases}$$
with no-flux boundary conditions $\partial_\nu u+\chi u\,\partial_\nu v-\xi S(u)\,\partial_\nu w=\partial_\nu v=0$. Here $u$ is the cell density, $v$ a signal produced by the cells that repels them (the sign $+\chi$), and $w$ a matrix degraded by the signal that attracts cells. The $C^2$ hapto-sensitivity satisfies, for some $\theta\in\mathbb{R}$,

$$0=S(0)\le S(u)\le u(u+1)^{\theta-1}\qquad(u\ge0).$$

Initial data: $u_0\in C(\bar\Omega)$, $u_0\ge0$, $u_0\not\equiv0$; $\tau v_0\in W^{1,\infty}(\Omega)$, $\tau v_0\ge0$; $w_0\in C^2(\bar\Omega)$, $w_0\ge0$, $\partial_\nu w_0=0$.

**Theorem.** In each of the following cases the problem has a unique global positive classical solution with $\sup_{t\ge0}\bigl(\|u(t)\|_{L^\infty}+\|v(t)\|_{W^{1,\infty}}+\|w(t)\|_{W^{1,\infty}}\bigr)<\infty$:

1. $n=2$, $\tau=1$, and $\theta<\tfrac32$, or $\theta<2$ with $\nabla\sqrt{w_0}\in L^\infty(\Omega)$.
2. $n\ge2$, $\tau=0$, $\chi>0$, and $\theta<\tfrac32$, or $\theta<2$ with $\nabla\sqrt{w_0}\in L^\infty(\Omega)$ (blow-up prevention by repulsion in every dimension).
3. Haptotaxis only, $\chi=0$, $n\ge3$: for $\tau=0$, $\theta<1+\tfrac1n$, or $\theta<1+\tfrac2n$ with $\nabla\sqrt{w_0}\in L^\infty$; for $\tau=1$, $\theta<\tfrac4n$ if $3\le n\le4$ and $\theta<\tfrac{6n-n^2-4}{2(n-2)}$ if $n\ge5$.

## Expansion

Solving the $w$-equation gives $w=w_0\exp(-\int_0^t v)$, so $\nabla w$ is controlled by $\nabla w_0$ and $\int_0^t\nabla v$, which turns the haptotactic term into a cross-diffusion term of chemotactic type. The repulsive sign of $\chi$ makes the chemotactic contribution to the $L^p$ energy of $u$ dissipative; the growth bound on $S$ with $\theta<\tfrac32$ (or $\theta<2$ using the extra regularity of $\sqrt{w_0}$) lets the haptotactic contribution be absorbed by diffusion. An $L^p$ bound with $p>n/2$ then upgrades to $L^\infty$ by Moser–Alikakos iteration and semigroup estimates.

## Sources

- Y. Chen, T. Xiang, "Global solvability, regularity and exponential convergence in a quasilinear chemotaxis-haptotaxis system with mostly repulsive signal production", arXiv:2611.22930 (2026), Section 1 (system and hypotheses on $S$ and the data), Theorem 1.1 (B1), (B2) and Theorem 1.2, Section 3, <https://doi.org/10.48550/arXiv.2611.22930>.
