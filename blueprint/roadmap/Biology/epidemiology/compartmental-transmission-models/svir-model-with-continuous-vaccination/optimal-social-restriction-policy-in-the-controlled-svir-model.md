# Optimal social-restriction policy in the controlled SVIR model

**Controlled model.** In the SVIR model with continuous vaccination, let a measurable restriction policy $u:[0,T]\to[0,\bar u]$, $\bar u\in[0,1]$, scale transmission through a decreasing linear function $\beta(u)$, and let vaccinees be infected at the reduced rate $\varepsilon\beta(u)$, $\varepsilon\ge0$:

$$S'=\mu-\beta(u)SI-(\alpha+\mu)S,\qquad V'=\alpha S-\varepsilon\beta(u)VI-(\gamma_1+\mu)V,\qquad I'=\beta(u)SI+\varepsilon\beta(u)VI-(\gamma+\mu)I .$$

The planner minimizes the cost of restrictions plus the costs of infection and of vaccination,

$$J(u)=\int_0^T\big[c(u(t))+c_1I(t)+c_2\alpha S(t)\big]dt,\qquad c_1,c_2>0,$$

where $c$ is $C^2$ with $c(0)=0$, $c'>0$, $c''>0$.

**Theorem (existence and optimality system).** An optimal control $u^*$ exists. With Hamiltonian $H=c(u)+c_1I+c_2\alpha S+\lambda_1S'+\lambda_2V'+\lambda_3I'$, an optimal $(S^*,V^*,I^*,u^*)$ satisfies the adjoint system

$$\lambda_1'=[\beta(u)I+\alpha+\mu]\lambda_1-\alpha\lambda_2-\beta(u)I\lambda_3-c_2\alpha,\qquad \lambda_2'=[\varepsilon\beta(u)I+\gamma_1+\mu]\lambda_2-\varepsilon\beta(u)I\lambda_3,$$

$$\lambda_3'=\beta(u)S\lambda_1+\varepsilon\beta(u)V\lambda_2-[\beta(u)S+\varepsilon\beta(u)V-\gamma-\mu]\lambda_3-c_1,$$

with $\lambda_1(T)=\lambda_2(T)=\lambda_3(T)=0$, and $u^*(t)$ minimizes $H(t,S,V,I,\cdot)$ over the admissible range.

**Corollaries (explicit policies for $\beta(u)=\beta_0(1-u)$).** Put $K(t)=S(\lambda_3-\lambda_1)+\varepsilon V(\lambda_3-\lambda_2)$.

1. Quadratic cost $c(u)=bu^2$: $u^*(t)=\min\{\max[0,\beta_0I(t)K(t)/(2b)],\bar u\}$.
2. Exponential cost $c(u)=e^{ku}-1$, when $\lambda_3>\lambda_1$ and $\lambda_3>\lambda_2$: $u^*(t)=\min\{\max[0,\frac1k\ln\frac{\beta_0I(t)K(t)}{k}],\bar u\}$ if $K(t)>0$, and $u^*(t)=0$ if $K(t)\le0$.
3. Linear cost $c(u)=au$: the optimal policy is bang-bang with a possible singular arc, $u^*=\bar u$ where $\partial H/\partial u<0$, $u^*=0$ where $\partial H/\partial u>0$, and a singular value $u_{\rm sing}$ on intervals where $\partial H/\partial u\equiv0$. (The source's (17) prints $u^*=1$, which leaves the admissible range when $\bar u<1$.)

## Depends on

- [Threshold dynamics of the SVIR model with continuous vaccination](threshold-dynamics-of-the-svir-model-with-continuous-vaccination.md)

## Expansion

Existence follows from the standard Filippov–Cesari argument: the control set is compact and convex, the state stays in the simplex, the dynamics are affine in $u$ and the integrand is convex in $u$. The adjoint equations are $\lambda_k'=-\partial H/\partial(\text{state }k)$ with free terminal state. For $\beta(u)=\beta_0(1-u)$, $\partial H/\partial u=c'(u)-\beta_0IK$, and strict convexity of $c$ makes the minimizer unique and given by the projected stationarity condition, which produces the quadratic and exponential formulas. The quantities $\lambda_3-\lambda_1$ and $\lambda_3-\lambda_2$ are shadow-price gaps: the marginal cost of one more susceptible, respectively vaccinee, becoming infected, so restrictions are tightened when infected individuals are many and these marginal costs are large. As $b\to0$ or $k\to0$ the policy tends to the strictest admissible level $\bar u$. With a linear cost the Hamiltonian is affine in $u$, so the switching function $\partial H/\partial u$ decides between the bounds, and the singular control is obtained by differentiating the switching function along the arc.

## Sources

- Alessandro Ramponi, M. Elisabetta Tessitore, "The economic cost of social distancing during a pandemic: an optimal control approach in the SVIR model", Decisions in Economics and Finance 48 (2025), 485–516, <https://doi.org/10.1007/s10203-023-00406-0>. Published version of arXiv:2208.04908, cited next; locators there refer to the arXiv version.
- A. Ramponi and M. E. Tessitore, "The economic cost of social distancing during a pandemic: an optimal control approach in the SVIR model", arXiv:2208.04908 (2022), Section 3 (controlled model, Theorem 3 on existence, Theorem 4 on the optimality system, Corollaries 6 and 7, Proposition 10) and Appendix 1 (proof of Proposition 10), <https://doi.org/10.48550/arXiv.2208.04908>.
