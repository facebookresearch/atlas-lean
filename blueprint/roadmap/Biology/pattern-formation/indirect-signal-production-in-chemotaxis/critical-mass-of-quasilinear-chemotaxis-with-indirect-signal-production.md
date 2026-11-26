# Critical mass of quasilinear chemotaxis with indirect signal production

**Model.** Let $d \ge 3$, $m = m_c = \frac{2(d-1)}{d}$ (the critical diffusion exponent), and $\mathbb{B}_R \subset \mathbb{R}^d$ a ball. Cells $u$ produce, at unit rate, an intermediate substance $w$ that does not diffuse; $w$ produces the chemoattractant $v$:

$$\partial_t u = \operatorname{div}\big(m(1+u)^{m-1}\nabla u - u\nabla v\big), \qquad -\Delta v + v = w, \qquad \partial_t w = u - w,$$

with homogeneous Neumann conditions for $u$ and $v$. For $p > 2d$ and nonnegative data $(u^0,w^0) \in W^1_p(\mathbb{B}_R)\times L_\infty(\mathbb{B}_R)$ there is a unique global nonnegative strong solution, the cell mass $\|u(t)\|_1 = \|u^0\|_1$ is conserved. With $\mathcal{K} = (1-\Delta_N)^{-1}$ (so $v = \mathcal{K}[w]$) and $\phi''(z) = m(1+z)^{m-1}/z$, $\phi(1) = \phi'(1) = 0$, the functional
$$\mathcal{L}(u,w) = \int_{\mathbb{B}_R}\big(\phi(u) - u\,\mathcal{K}[w]\big)\,dx + \frac12\|\nabla\mathcal{K}[w]\|_2^2 + \frac12\|\mathcal{K}[w]\|_2^2$$
is a strict Lyapunov functional, with dissipation $\int u|\nabla(\phi'(u) - \mathcal{K}[w])|^2 + \|\nabla\mathcal{K}[u-w]\|_2^2 + \|\mathcal{K}[u-w]\|_2^2$.

**Critical mass.** Let $\zeta$ be the unique radially symmetric classical solution of
$$-\Delta\zeta = \frac{m-1}{m}\zeta^{1/(m-1)} \ \text{ in } \mathbb{B}_1, \qquad \zeta = 0 \ \text{ on } \partial\mathbb{B}_1,$$
and set $M_c = \int_{\mathbb{B}_1}\zeta^{1/(m-1)}\,dx$. Equivalently, $M_c$ is determined by the optimal constant of the variant of the Hardy-Littlewood-Sobolev inequality bounding $\int h\,(E_d * h)$ by $\|h\|_1^{2/d}\|h\|_m^m$, $E_d$ the Newtonian kernel; it is the critical mass of the quasilinear Patlak-Keller-Segel model with critical nonlinear diffusion.

**Theorem.** In the radially symmetric setting, the threshold masses for boundedness and unboundedness coincide and equal $M_c$:
1. If the cell mass $M = \|u^0\|_1$ of radial data satisfies $M < M_c$, the global solution is bounded.
2. If $M > M_c$, there is $\mu^s_M$ such that the set of radial initial data of mass $M$ with $\mathcal{L}(u^0,w^0) < \mu^s_M$ is nonempty, and every solution from it blows up in infinite time.

## Expansion

Indirect production through the non-diffusing $w$ delays aggregation: solutions are always global (no finite-time blow-up), and the question is boundedness versus infinite-time blow-up. Below $M_c$, the HLS-type inequality makes the Lyapunov functional coercive, bounding $u$ in $L_m$ and then in $L_\infty$. Above $M_c$, a detailed study of the radial stationary states gives an energy level $\mu^s_M$ below all steady states of mass $M$; since $\mathcal{L}$ decreases strictly, a solution started below that level cannot converge to a steady state, and compactness of bounded trajectories then forces unboundedness. The threshold is the same as for direct signal production, so the extra kinetic step changes the blow-up time scale, not the mass criterion.

## Sources

- Philippe Laurençot and Christoph Walker, "Identifying the critical mass in a quasilinear chemotaxis model with indirect signal production", arXiv:2611.32580 (2026), Section 2, Theorem 2.1, Proposition 2.2 and Theorem 2.3, <https://doi.org/10.48550/arXiv.2611.32580>.
