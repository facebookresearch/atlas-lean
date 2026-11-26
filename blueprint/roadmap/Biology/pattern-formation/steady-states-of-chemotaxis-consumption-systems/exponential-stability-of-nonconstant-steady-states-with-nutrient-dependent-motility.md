# Exponential stability of nonconstant steady states with nutrient-dependent motility

**Model.** On a bounded domain $\Omega$ in two or three dimensions ($C^4$ boundary), or an interval, a population $u$ moves with nutrient-dependent motility $\phi(w)$ and consumes a nutrient $w$ supplied at a fixed boundary concentration $b > 0$:

$$u_t = \Delta\big(u\phi(w)\big), \qquad w_t = D\Delta w - uw, \qquad \partial_\nu\big(u\phi(w)\big) = 0, \quad w|_{\partial\Omega} = b.$$

The population mass $\mu = \int_\Omega u\,dx$ is conserved. **Motility assumption:** $\phi \in C([0,\infty))\cap C^3((0,\infty))$, $\phi(0) = 0$, $\phi > 0$ on $(0,\infty)$, and
$$0 \le s\phi'(s) \le \phi(s), \qquad 0 < s \le b,$$
i.e. both $\phi$ and $s/\phi(s)$ are nondecreasing on $(0,b]$ (power laws $s^\alpha$, $0<\alpha\le1$, saturating laws, and $s^\alpha/(1+s)^\beta$ with $0\le\beta\le\alpha\le1$); in several dimensions also $\phi \in C^5$ on $[b/4, 5b/4]$.

**Steady states.** A steady state of mass $\mu$ solves $U\phi(W) = Z_\mu$ (constant), $D\Delta W = UW$, $W|_{\partial\Omega} = b$, $\int U = \mu$. With $\tau$ the Dirichlet torsion function ($-\Delta\tau = 1$, $\tau|_{\partial\Omega} = 0$), it exists, is unique and satisfies $b/2 \le W \le b$ when $D \ge D_{\rm pos}(\mu) = \frac{2\mu}{|\Omega|}\|\tau\|_\infty$. It is nonconstant, since the nutrient is depleted in the interior.

**Theorem.** Fix $m > 0$ and $D > D_3(m)$, an explicit threshold built from $D_{\rm pos}$, $|\Omega|$, the first Dirichlet eigenvalue and bounds on $\phi$, $\phi'$. There are $r_m, \delta, C, \omega > 0$ such that every mass $\mu \in [m - r_m, m + r_m]$ has a unique positive steady state $(U_\mu, W_\mu)$, and for compatible initial data ($w_0|_{\partial\Omega} = b$, $(D\Delta w_0 - bu_0)|_{\partial\Omega} = 0$) with
$$d_0 = \|u_0 - U_m\|_{H^1} + \|w_0 - W_m\|_{H^3} < \delta,$$
the solution is global, unique, satisfies $b/4 \le w \le 5b/4$, and converges exponentially to the steady state with the **initial mass** $\mu_0 = \int u_0$:
$$\|u(t) - U_{\mu_0}\|_{H^1} + \|w(t) - W_{\mu_0}\|_{H^3} \le Ce^{-\omega t}d_0.$$
The selected equilibrium depends locally Lipschitz-continuously on the data, and $u_0 \ge 0$ implies $u(t) \ge 0$. A lower-regularity version holds on an interval.

## Expansion

Because mass is conserved, the steady states form a one-parameter family indexed by $\mu$, and a perturbation changing the mass must converge to a different member of the family (mass selection) rather than back to $U_m$. The proof writes $u - U_{\mu_0} = -\Delta q$ with a Neumann potential $q$ and $\psi = w - W_{\mu_0}$, and builds a nonlinear potential energy for $(q,\psi)$ whose dissipation controls $\|Q\|_{H^3}$; large $D$ makes the nutrient nearly constant, so the coupling terms are small relative to diffusion. To first order in $D^{-1}$, the nutrient deficit is $b - W \approx \frac{b\mu}{D|\Omega|}\tau$, the torsion function times the mean population density and the boundary value, and the population contrast is governed by the elasticity $\kappa_b = b\phi'(b)/\phi(b) \in [0,1]$.

## Sources

- Xinyu Cheng, Xuewen Lai and Xu Song, "Nonlinear Stability of Nonconstant Steady States in Chemotaxis--Consumption Systems with General Motility", arXiv:2609.34202 (2026), Section 2 (Motility assumption and the theorem "Nonlinear stability and mass selection") and Section 3, <https://doi.org/10.48550/arXiv.2609.34202>.
