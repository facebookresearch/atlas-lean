# Global weak solutions of degenerate chemotaxis with indirect signal production

**Model.** On the whole space $\mathbb R^d$, consider the fully parabolic degenerate chemotaxis system with indirect signal production, $m>1$:
$$\partial_t u = \operatorname{div}\big(\nabla u^m - u\nabla v\big), \qquad \partial_t v = \Delta v - v + w, \qquad \partial_t w = \Delta w - w + u,$$
with non-negative data $u_0 \in \mathcal P_2(\mathbb R^d) \cap L^\infty$ of mass $M$ (finite second moment), $v_0, w_0 \in W^{2,m}\cap W^{2,\infty}$. Dimensional analysis gives the critical exponent
$$m^* = \frac{2(d-2)}{d},$$
which separates diffusion-dominated ($m>m^*$) from aggregation-dominated ($m<m^*$) behavior; for $d \le 4$, $m^* \le 1$.

**Theorem.** A global weak solution exists and is bounded, $u \in L^\infty((0,\infty)\times\mathbb R^d)$, $v \in L^\infty(0,\infty;W^{2,\infty})$, $w \in L^\infty(0,\infty;W^{1,\infty})$, in each of the following cases:

1. **Subcritical:** $1 \le d \le 4$, or $d \ge 5$ and $m > m^*$, for any data;
2. **Critical:** $d \ge 5$, $m = m^*$ and $M < M^* = (m^*-1)K_{m^*}^2/2$, where
$$K_{m^*}^2 = \sup\Big\{\frac{\int_{\mathbb R^d} u\,(-\Delta)^{-2}u\,dx}{\|u\|_{m^*}^{m^*}} : u \in L^1_+\cap L^{m^*},\ \|u\|_1 = 1\Big\};$$
3. **Supercritical:** $d \ge 5$, $m$ in a range $(m_*,m^*)$ below the critical exponent and $\|u_0\|_m^m$ smaller than an explicit constant depending on $d$, $m$, $M$; then also $\|u(t)\|_m \le \|u_0\|_m$ for all $t$.

## Expansion

Solutions are built from a time-discrete scheme: the $u$-step is a JKO (minimizing movement) step for the 2-Wasserstein gradient flow of $\frac{1}{m-1}\int u^m - \int uv$, while the $v$ and $w$ steps are $L^2$ minimizations. Since the signal kernel of the indirect cascade behaves like $(-\Delta)^{-2}$, the interaction is controlled by the functional inequality defining $K_{m^*}$, which explains the threshold mass. Uniform estimates come from the flow interchange method and discrete maximal regularity, and pass to the limit as the time step vanishes.

## Sources

- Tatsuya Hosono and Philippe Laurençot, "Global existence and boundedness for a degenerate chemotaxis system with indirect signal production via minimizing movement schemes", arXiv:2607.21211 (2026), Theorem 1.2 and Corollary 2.4, with Theorem 2.9 and Propositions 3.1–3.3, <https://doi.org/10.48550/arXiv.2607.21211>.
