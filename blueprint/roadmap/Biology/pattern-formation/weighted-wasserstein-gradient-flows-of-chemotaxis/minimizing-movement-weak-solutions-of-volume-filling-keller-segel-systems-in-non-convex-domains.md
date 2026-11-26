# Minimizing-movement weak solutions of volume-filling Keller–Segel systems in non-convex domains

**Model.** Let $\Omega \subset \mathbb{R}^d$, $d \ge 2$, be a bounded domain with smooth boundary, not necessarily convex, and let $p \ge 1$, $0 < \alpha < 1$, $\chi > 0$. Consider the quasilinear Keller–Segel system with nonlinear mobility (volume filling)

$$\partial_t u = \Delta u^p - \nabla\cdot(\chi u^\alpha\nabla v), \qquad \partial_t v = \Delta v - v + u,$$

with $\nabla u\cdot n = \nabla v\cdot n = 0$ on $\partial\Omega$, a nonnegative probability density $u_0 \in L^{p+1-\alpha}(\Omega)$ and $0 \le v_0 \in H^1(\Omega)$. For a concave mobility $m$, the weighted Wasserstein distance is

$$W_m(\mu_0,\mu_1)^2 = \inf\Big\{\int_0^1\!\!\int \frac{|\nu|^2}{m(\mu)}\,dx\,dt : \partial_t\mu + \nabla\cdot\nu = 0,\ \mu(0) = \mu_0,\ \mu(1) = \mu_1\Big\},$$

which reduces to the Wasserstein distance (Benamou–Brenier) when $m(r) = r$.

**Theorem.** Suppose $1 + \alpha - 2/d < p \le 1 + \alpha$, or $p = 1 + \alpha - 2/d$ with $\chi$ small enough. Then for every $T > 0$ there is a nonnegative weak solution $(u,v)$ on $[0,T]$ with
- $u \in L^\infty(0,T;L^{p+1-\alpha}(\Omega))$, $u^{(p+1-\alpha)/2} \in L^2(0,T;H^1(\Omega))$ and $\|u(t)\|_{L^1} = 1$;
- $v \in L^\infty(0,T;H^1)\cap L^2(0,T;H^2)\cap C^{1/2}([0,T];L^2)$;
- $W_m(u(t),u_0) \to 0$ with $m(u) = u^\alpha$, and $v(t) \to v_0$ in $L^2$, as $t \to 0$;
- for all $\varphi \in C^\infty(\overline\Omega)$ with $\nabla\varphi\cdot n = 0$ and all $\zeta \in H^1(\Omega)$,

$$\int_0^T\!\!\int_\Omega(\nabla u^p - \chi u^\alpha\nabla v)\cdot\nabla\varphi = \int_\Omega(u_0 - u(T))\varphi, \qquad \int_0^T\!\!\int_\Omega \nabla v\cdot\nabla\zeta + v\zeta - u\zeta = \int_\Omega(v_0 - v(T))\zeta.$$

The solution is constructed by a minimizing-movement scheme in weighted Wasserstein metrics, previously available only on convex domains; the degenerate critical case $p = 1 + \alpha - 2/d$ on non-convex domains is new.

## Expansion

The key ingredient is an evolution variational inequality valid without convexity of $\Omega$. For a regularized mobility $m_\varepsilon(r) = m(r + \varepsilon)$ satisfying $\sup|m_\varepsilon'| < \infty$, $\sup|m_\varepsilon''m_\varepsilon| < \infty$ and $\sup|m_\varepsilon'|^2/|m_\varepsilon''m_\varepsilon| < \infty$ (true for $m(r) = r^\alpha$), the auxiliary functional $F(u) = \int_\Omega u\varphi + \delta\int_\Omega U_\varepsilon(u)$ with $U_\varepsilon''m_\varepsilon = 1$ and its flow $\partial_t\rho = \delta\Delta\rho + \nabla\cdot(m_\varepsilon(\rho)\nabla\varphi)$, $S_t$, satisfy

$$\frac12\limsup_{h\downarrow0}\frac{W_{m_\varepsilon}(S_h u, w)^2 - W_{m_\varepsilon}(u,w)^2}{h} + \frac{\lambda_\delta}{2}W_{m_\varepsilon}(u,w)^2 \le F(w) - F(u)$$

for an explicit $\lambda_\delta \le 0$. In convex domains the boundary term in the derivative of the action has a sign; in non-convex domains it is controlled by $\nabla(|\nabla w|^2)\cdot n \le C_\Omega|\nabla w|^2$ on $\partial\Omega$, the Sobolev trace embedding, a fractional Gagliardo–Nirenberg inequality and Kato's inequality $|\nabla|\nabla w|| \le |\nabla^2 w|$, and then absorbed. Testing the minimizing-movement scheme with $S_h$ (flow interchange) gives the Euler–Lagrange equation and the extra regularity needed to pass to the limit.

## Sources

- K. Murai, "The evolution variational inequality for weighted Wasserstein metrics in non-convex bounded domains", arXiv:2605.13420 (2026), Theorem 4.1 (Keller–Segel application), with Theorem 3.3, Corollary 3.4 and Lemmas 2.1–2.4, <https://doi.org/10.48550/arXiv.2605.13420>.
