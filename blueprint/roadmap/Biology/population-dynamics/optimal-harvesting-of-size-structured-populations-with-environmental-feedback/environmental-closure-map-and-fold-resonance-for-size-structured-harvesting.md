# Environmental closure map and fold resonance for size-structured harvesting

**Model.** On the size interval $\Omega = [l_0, l_m] \subset (0,\infty)$ let $x(t,l) \ge 0$ be the population density, $\chi \in L^\infty_+(\Omega)$, $\chi \not\equiv 0$, an environmental weight, and $E(t) = \int_\Omega \chi(l) x(t,l)\,dl$ the scalar environmental output. Individual growth $g(E,l) \ge g_m > 0$ and mortality $\mu(E,l) \ge 0$ depend on $E$, harvesting acts at size-dependent rate $u(t,l) \in [0, u_{\max}]$, and recruits enter at a fixed flux $p(t) > 0$:
$$\partial_t x + \partial_l\bigl(g(E(t),l)\, x\bigr) = -\bigl(\mu(E(t),l) + u(t,l)\bigr) x, \qquad g(E(t),l_0)\, x(t,l_0) = p(t).$$
Under boundedness and Lipschitz assumptions on $g, \mu$ in $(E,l)$ (Assumptions 2.1-2.2) and bounded-variation controls and inflows, the system has a unique global nonnegative weak solution in $C^0(\mathbb{R}_+; L^1_+(\Omega))$ with $\|x(t)\|_{L^1} \le \|x_0\|_{L^1} + p_{\max} t$, Lipschitz in the initial state, and defines a forward-complete positive control system with the cocycle property (Theorems 3.1 and 3.2).

**Stationary profile and closure map (Proposition 3.3).** For a stationary harvest $u(l)$, constant inflow $p$ and frozen level $E \ge 0$, the stationary problem has the unique nonnegative solution
$$x_E(l) = \frac{p}{g(E,l)} \exp\Bigl[-\int_{l_0}^{l} \frac{\mu(E,\xi) + u(\xi)}{g(E,\xi)}\,d\xi\Bigr],$$
and $(x_{E^*}, E^*)$ is a stationary state if and only if $E^*$ solves the scalar **closure equation**
$$E^* = \Phi_u(E^*), \qquad \Phi_u(E) := \int_\Omega \chi(l)\, x_E(l)\,dl.$$
Since $\Phi_u(0) > 0$ and $E - \Phi_u(E) \to +\infty$, a root always exists.

**Theorem 3.4 (closure derivative).** $E \mapsto \Phi_u(E)$ is $C^1$ and, with $\alpha_u = -\partial_E \log g$ and $b_u = \partial_E\bigl((\mu + u)/g\bigr)$,
$$\Phi_u'(E) = \int_\Omega \chi x_E \alpha_u\,dl - \int_{l_0}^{l_m} b_u(E,\xi)\Bigl(\int_\xi^{l_m} \chi x_E\,dl\Bigr) d\xi,$$
a growth-response term minus a cumulative hazard-response term.

**Definition 3.5 and Theorem 3.6 (fold resonance).** A root $E^*$ is *nonresonant* if $1 - \Phi_u'(E^*) \ne 0$ and *resonant* if $\Phi_u'(E^*) = 1$. For a parameter $\eta$ and $H(E,\eta) = E - \Phi(E,\eta)$: at a nonresonant root there is a local $C^2$ branch with
$$E'(\eta) = \frac{\partial_\eta \Phi}{1 - \partial_E \Phi};$$
at a resonant root with $\partial_{EE} H \ne 0$ and $\partial_\eta H \ne 0$ the equilibria form a nondegenerate fold,
$$E_\pm(\eta) = E^* \pm \Bigl[-\frac{2\,\partial_\eta H}{\partial_{EE} H}(\eta - \eta^*)\Bigr]^{1/2} + o(|\eta - \eta^*|^{1/2}).$$

**Theorems 3.7 and 3.8 (existence of an optimal stationary policy).** Let the admissible harvests be $\mathcal U = \{u \in BV(\Omega) : 0 \le u \le u_{\max},\ \mathrm{TV}(u) \le M_u\}$, compact in $L^1$, and suppose a branch $u \mapsto E^*_u$ of roots is uniformly nonresonant: $E^*_u \le E_{\max}$, $s(1 - \partial_E\Phi_u) \ge \gamma > 0$ near $E^*_u$ for a fixed sign $s$, and $E^*_u$ is the only root nearby (Assumption 2.4). Then $u \mapsto E^*_u$ is Lipschitz in $L^1$, $|E^*_{u_1} - E^*_{u_2}| \le C\,\|u_1 - u_2\|_{L^1}/(\gamma g_m)$, and the stationary yield $\mathcal Y(u) = \int_\Omega \pi(l)\, u(l)\, x^*_u(l)\,dl$ with unit value $\pi \in L^\infty_+(\Omega)$ has a maximizer on $\mathcal U$.

## Expansion

The stationary equation is a linear first-order ODE in $l$ for the flux $g_E x_E$ with hazard $(\mu + u)/g$, which gives the explicit profile, so the whole infinite-dimensional equilibrium problem reduces to one scalar equation in $E$. Differentiating the profile in $E$ gives $\partial_E x_E = x_E[\alpha_u - \int_{l_0}^l b_u]$, and integrating against $\chi$ (with Fubini on the second term) gives the closure derivative. The fold statement is the implicit function theorem away from resonance and a second-order expansion at it. On a uniformly nonresonant branch, the implicit function estimate gives Lipschitz dependence of $E^*_u$ on $u$, hence continuity of the yield on the $L^1$-compact admissible set, and a maximizer exists by the direct method.

## Sources

- L. S. Wang, J. Yu, "Optimal harvesting of size-structured populations with environmental feedback and fixed recruitment flux" (2026), Section 2 (model, Assumptions 2.1, 2.2 and 2.4, Definition 2.3), Section 3 (Theorems 3.1, 3.2, 3.4, 3.6, 3.7 and 3.8, Proposition 3.3, Definition 3.5), <https://doi.org/10.48550/arXiv.2607.03790>.
