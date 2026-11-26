# Critical mass $8\pi$ for infinite-time blow-up in Keller–Segel with indirect signal production on surfaces

Let $(\Sigma,g)$ be a closed connected Riemannian surface. Consider the parabolic–elliptic–ODE chemotaxis system with indirect signal production

$$\begin{cases}
\partial_tu=\Delta_gu-\operatorname{div}_g(u\nabla_gv),\\
0=\Delta_gv-\overline w+w,\qquad \int_\Sigma v\,d\mu_g=0,\\
\partial_tw=-w+u,
\end{cases}$$

with nonnegative $u_0\in C(\Sigma)$, $w_0\in C^1(\Sigma)$, where $\overline w$ is the spatial mean of $w$ and $M=\int_\Sigma u_0\,d\mu_g$ is the conserved cell mass.

**Theorem.**

1. (Global existence) A unique global classical solution exists for all such data; no finite-time blow-up occurs.
2. (Subcritical mass) If $M<8\pi$, then $\|u(t)\|_{L^\infty}+\|w(t)\|_{L^\infty}+\|v(t)\|_{W^{1,\infty}}\le C$ for all $t\ge0$.
3. (Supercritical mass) For every $M>8\pi$ there are strictly positive smooth $u_0,w_0$ with $\int_\Sigma u_0\,d\mu_g=M$ and $\limsup_{t\to\infty}\|u(t)\|_{L^\infty}=\infty$ (infinite-time blow-up).
4. (Planar Neumann problem) In a smooth bounded domain $\Omega\subset\mathbb R^2$ with no-flux boundary conditions, for every $M>4\pi$ there are smooth data of mass $M$ whose solutions blow up in infinite time.
5. (Critical mass) If $\Sigma$ is a round sphere and $M=8\pi$, solutions remain globally bounded; on the Riemann sphere with a suitable rotation-invariant metric there are data of mass $8\pi$ with $\|u(t)\|_{L^\infty}\ge1000+t/2000$ for all $t\ge0$.

## Expansion

Integrating the $w$-equation gives $\overline w(t)=e^{-t}\overline{w_0}+(1-e^{-t})M/\mu_g(\Sigma)$, and $w$ is a time-smoothed copy of $u$; this delay removes finite-time collapse, unlike the classical Keller–Segel model where mass above $8\pi$ can concentrate in finite time. The system has a Lyapunov functional $\mathcal E_g(u,v)=\int_\Sigma u\log u-\int_\Sigma uv+\frac12\int_\Sigma|\nabla_gv|^2$ plus a nonnegative dissipation term. For $M<8\pi$ the Moser–Trudinger inequality on surfaces bounds $\mathcal E_g$ below and yields uniform bounds. For $M>8\pi$ one shows that the infimum of $\mathcal E_g$ over steady states of mass $M$ is finite while suitable initial data have energy below it; a bounded global solution would converge along a sequence to a steady state, a contradiction. On a planar domain boundary concentration costs only half the mass, which gives the threshold $4\pi$. At $M=8\pi$ the outcome depends on the geometry: on the round sphere the sharp Moser–Trudinger inequality still controls the energy, while a non-round metric admits grow-up.

## Sources

- Jing Li, Yuxiang Li, "Critical mass for infinite-time blow-up in a Keller-Segel system with indirect signal production on closed Riemannian surfaces", arXiv:2611.16572 (2026), Proposition 1.1, Theorems 1.2–1.6, Proposition 3.1, Propositions 6.2 and 7.1, <https://doi.org/10.48550/arXiv.2611.16572>.
