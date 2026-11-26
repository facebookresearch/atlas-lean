# Minimum-size harvesting policy from single-crossing switching functions

**Control problem.** The size-structured population $\partial_t x + \partial_l(g(E,l)x) = -(\mu(E,l)+u(t,l))x$ on $(0,T)\times(l_0,l_m)$, with environment $E(t) = \int\chi x\,dl$, initial density $\phi$ and inflow $g(E,l_0)x(t,l_0) = p(t)$, is harvested with fishing mortality $u(t,l) \in [0,u_{\max}]$ (with a bound $C_u$ on its spatial total variation) to maximize the discounted yield
$$J_T(u) = \int_0^T e^{-rt}\int_{l_0}^{l_m} c(l)\,u(t,l)\,x(t,l)\,dl\,dt, \qquad r>0,$$
where $c(l) \ge 0$ is the value per harvested individual. The first variation is $J_T'(u^*)h = \int_0^T e^{-rt}\int x^* S^* h$, with switching function $S^*(t,l) = c(l) - \lambda^*(t,l)$ and $\lambda^*$ the adjoint (shadow value of a live individual).

**Theorem (bang–bang).** If the variation constraint is inactive with a uniform margin, then wherever $x^*(t,l)>0$,
$$u^*(t,l) = \begin{cases} 0, & S^*(t,l) < 0,\\ u_{\max}, & S^*(t,l) > 0,\end{cases}$$
and $u^*$ is not determined on the singular set $\{S^* = 0\}$.

**Theorem (strict minimum-size policy).** If moreover $S^*(t,\cdot)$ is strictly upward single crossing for a.e. $t$, then for a.e. $t$ exactly one holds: $S^*<0$ and $u^*=0$; $S^*>0$ and $u^* = u_{\max}$; or there is a unique $L^*(t) \in (l_0,l_m)$ with $S^*(t,L^*(t)) = 0$ and
$$u^*(t,l) = u_{\max}\,\mathbf 1_{\{l > L^*(t)\}} \quad \text{a.e.}$$
Where $S^* \in C^1$ crosses transversally, $L^*$ is locally $C^1$ with $\dot L^*(t) = -\partial_t S^*/\partial_l S^*$ at $(t,L^*(t))$. Strict monotonicity of $S$ is sufficient for single crossing but not necessary, and monotone value $c(l)$ alone does not imply a threshold policy because $\lambda^*$ may be non-monotone in size.

## Depends on

- [Integrated monotonicity certificate for the stationary environment](integrated-monotonicity-certificate-for-the-stationary-environment.md)

## Expansion

The payoff is affine in $u$, so the variational inequality $\int e^{-rt}\int x^* S^*(v-u^*) \le 0$ reduces pointwise to maximizing $v\,x^* S^*$ over $v \in [0,u_{\max}]$ when the variation budget does not bind. A single upward zero of $S^*(t,\cdot)$ then splits sizes into a protected juvenile range and a fully harvested adult range. The environmental feedback enters $S^*$ through a rank-one correction of the adjoint, which the paper controls by small-feedback and validated interval certificates.

## Sources

- Louis Shuo Wang, "Vital-Rate Feedback and Threshold Harvesting in Size-Structured Populations", arXiv:2606.25288 (2026), Proposition 7.7 (adjoint representation), Theorem 7.9 (bang–bang), Theorem 8.7 (strict minimum-size policy), Propositions 8.9 and 8.10, <https://doi.org/10.48550/arXiv.2606.25288>.
