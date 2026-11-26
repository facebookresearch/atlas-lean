# Integrated monotonicity certificate for the stationary environment

**Model.** A size-structured population with density $x(t,l)$ on sizes $l \in \Omega = (l_0,l_m)$ feels a scalar environment $E(t) = \int_{l_0}^{l_m}\chi(l)\,x(t,l)\,dl$ (weighted crowding, $\chi \in L^\infty_+$) through its vital rates:
$$\partial_t x + \partial_l\big(g(E,l)\,x\big) = -\big(\mu(E,l)+u(l)\big)\,x, \qquad g(E,l_0)\,x(t,l_0) = p,$$
with growth $g \ge g_{\min}(M) > 0$ on $[0,M]\times\Omega$, mortality $\mu \ge 0$, a fixed harvesting mortality $0 \le u \le u_{\max}$, and constant recruitment flux $p>0$. Crowding slows growth and raises mortality: $\partial_E g \le 0$, $\partial_E\mu \ge 0$.

**Frozen-environment profile.** For fixed $E$ the unique stationary profile is
$$x_E(l) = \frac{p}{g(E,l)}\exp\!\Big(-\int_{l_0}^{l}\frac{\mu(E,\xi)+u(\xi)}{g(E,\xi)}\,d\xi\Big),$$
and stationary states are the fixed points of the closure map $\Phi(E) = \int_{l_0}^{l_m}\chi(l)\,x_E(l)\,dl$. If $\Phi([0,M_{\rm st}]) \subseteq [0,M_{\rm st}]$ for some $M_{\rm st}>0$, at least one fixed point exists.

**Pointwise monotonicity fails at the inflow.** Since $x_E(l_0) = p/g(E,l_0)$,
$$\partial_E x_E(l_0) = -\frac{p\,\partial_E g(E,l_0)}{g(E,l_0)^2} \ge 0,$$
strictly positive whenever growth is strictly crowding-suppressed at $l_0$; so the profile cannot decrease in $E$ at every size.

**Theorem (integrated monotonicity).** With $\alpha(E,l) = -\partial_E g/g \ge 0$, $b(E,l) = \partial_E\big[(\mu+u)/g\big] \ge 0$ and the tail load $W_E(\xi) = \int_\xi^{l_m}\chi x_E\,dl$,
$$\Phi'(E) = \underbrace{\int_{l_0}^{l_m}\chi(l)\,x_E(l)\,\alpha(E,l)\,dl}_{\mathsf A(E)} \;-\; \underbrace{\int_{l_0}^{l_m} b(E,\xi)\,W_E(\xi)\,d\xi}_{\mathsf C(E)}.$$
If $\mathsf C(E) > \mathsf A(E)$ for every $E \in [0,M_{\rm st}]$, then $\Phi$ is strictly decreasing there and $E = \Phi(E)$ has exactly one solution $E^*$, with unique stationary profile $x^* = x_{E^*}$. If $\mathsf C - \mathsf A \ge \kappa > 0$, then $\Phi' \le -\kappa$ and the certificate is robust to perturbations that keep the margin. The condition is sufficient, not necessary.

## Expansion

The log-derivative $\partial_E \log x_E(l) = \alpha(E,l) - \int_{l_0}^l b(E,\xi)\,d\xi$ splits the response into a local residence-time gain (slower growth keeps individuals longer at each size) and a cumulative survival loss. Integrating against $\chi x_E$ and exchanging the order of integration (Fubini) turns the cumulative term into $\int b\,W_E$, which may dominate even though $\partial_E x_E > 0$ near $l_0$. The quantity $\mathsf A - \mathsf C = \Phi'(E^*)$ also reappears as the zero-discount feedback gain in the paper's adjoint analysis.

## Sources

- Louis Shuo Wang, "Vital-Rate Feedback and Threshold Harvesting in Size-Structured Populations", arXiv:2606.25288 (2026), Section 3: Proposition 3.1 (frozen-environment profile), Proposition 3.2 (existence of a stationary environment), Proposition 3.5 (failure of pointwise monotonicity), Theorem 3.7 and Corollary 3.8 (integrated monotonicity), <https://doi.org/10.48550/arXiv.2606.25288>.
