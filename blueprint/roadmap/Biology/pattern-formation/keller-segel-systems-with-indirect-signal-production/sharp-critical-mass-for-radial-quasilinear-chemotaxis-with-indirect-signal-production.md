# Sharp critical mass for radial quasilinear chemotaxis with indirect signal production

**Model.** In a ball $\mathbb B_R \subset \mathbb R^d$, $d \ge 3$, with no-flux boundary conditions,
$$\partial_t u = \operatorname{div}\big(m(1+u)^{m-1}\nabla u - u\nabla v\big), \qquad 0 = \Delta v + w - \langle w\rangle,\ \ \langle v\rangle = 0, \qquad \partial_t w = u - w,$$
where $\langle f\rangle$ is the spatial mean and the diffusion exponent is critical, $m = m_c = \frac{2(d-1)}{d} \in (1,2)$. Solutions with radially symmetric data $(u^0,w^0)$, $\|u^0\|_1 = M$, $\|w^0\|_1 \le \bar M$ ($\bar M \ge M$), are global and conserve $M$; the Lyapunov functional
$$\mathcal L(u,w) = \int_{\mathbb B_R}\big(\phi(u) - u\,v\big)\,dx + \frac12\int_{\mathbb B_R}|\nabla v|^2\,dx, \qquad v = \mathcal K[w - \langle w\rangle],$$
with $\phi''(r) = m(1+r)^{m-1}/r$ and $\mathcal K$ the Neumann inverse Laplacian, is non-increasing along trajectories.

**Critical mass.** Let $E_d(x) = c_d|x|^{2-d}$, $c_d = \frac{1}{(d-2)\sigma_d}$, be the Newton potential and $C_*$ the best constant of the Hardy–Littlewood–Sobolev variant
$$\int_{\mathbb R^d} h\,(E_d * h)\,dx \le c_d\,C_*\,\|h\|_{1}^{2/d}\,\|h\|_{m}^{m},$$
and set
$$M_c = \Big[\frac{2}{(m-1)\,c_d\,C_*}\Big]^{d/2},$$
the critical mass of the quasilinear Patlak–Keller–Segel model $\partial_t u = \operatorname{div}(\nabla u^m - u\nabla(E_d*u))$.

**Theorem.** (I) If $M \in (0,M_c)$, every radial solution is bounded. (II) If $M > M_c$, there is $\mu^s_M \in \mathbb R$ such that the set of radial data with mass $M$ and $\mathcal L(u^0,w^0) < \mu^s_M$ is non-empty, and every such solution is global but unbounded: it blows up in infinite time.

## Expansion

Indirect production delays signal build-up, so finite-time blow-up is replaced by infinite-time blow-up. The key is a dichotomy for stationary states: any sequence of radial steady states with $\mathcal L \to -\infty$ forces $M = M_c$, so for $M \ne M_c$ steady-state energies are bounded below by $\mu^s_M$. For $M<M_c$ the HLS inequality bounds $\mathcal L$ from below and gives compactness; for $M>M_c$, data with energy below every steady-state level cannot converge to a steady state, and boundedness would force such convergence via the Lyapunov structure. Concentration profiles of unbounded radial sequences converge, after rescaling, to the extremals of the HLS variant.

## Sources

- Philippe Laurençot and Christoph Walker, "A sharp mass threshold for boundedness in a critical quasilinear chemotaxis model with indirect signal production: the radially symmetric case", arXiv:2609.03713 (2026), Theorem 2.1 (well-posedness), Proposition 2.2 (Lyapunov functional), Theorem 2.3 (critical mass), Propositions 4.4 and 6.8 and Corollary 6.9, <https://doi.org/10.48550/arXiv.2609.03713>.
