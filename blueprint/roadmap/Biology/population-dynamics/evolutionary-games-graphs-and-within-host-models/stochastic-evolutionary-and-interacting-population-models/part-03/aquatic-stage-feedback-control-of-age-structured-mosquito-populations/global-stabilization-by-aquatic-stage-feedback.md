# Global stabilization of an age-structured logistic mosquito model by aquatic-stage feedback

**Model.** Mosquitoes are split into an aquatic (immature) cohort $I(a,t)$, adult females $F(a,t)$ and adult males $M(a,t)$, with age $a\in(0,A)$. Only the aquatic stage is controlled, by an additional removal rate $P(t)\ge0$ (larvivorous predators, drainage, habitat management):

$$\partial_tI+\partial_aI+\mu\bigl(a,p(t)\bigr)I=\Gamma(t)\,I\Bigl(1-\frac{\gamma(t)}{K(t)}\int_0^AI\,da\Bigr)-P(t)\,I,$$

$$\partial_tF+\partial_aF+\mu_F(a)F=-\gamma(t)F\int_0^AF\,da,\qquad \partial_tM+\partial_aM+\mu_M(a)M=-\gamma(t)M\int_0^AM\,da,$$

with $p(t)=\int_0^AI(a,t)\,da$, egg laying $I(0,t)=\int_0^A\beta(a,m(t))F(a,t)\,da$ modulated by the effective male density $m(t)=\int_0^A\lambda(a)M(a,t)\,da$, and emergence $F(0,t)=r\int_0^Aw(a)I(a,t)\,da$, $M(0,t)=(1-r)\int_0^Aw(a)I(a,t)\,da$ with sex ratio $r\in(0,1)$. Here $\Gamma$, $\gamma$, $K$ are positive time-varying growth, competition and carrying-capacity coefficients with means $\Gamma^\ast,\gamma^\ast,K^\ast$; the model is well posed in $L^2(0,A)^3$.

**Equilibrium and coordinates.** For a constant control $P^\ast$ in an explicit interval $(0,\zeta_I+\Gamma^\ast)$ determined by the model data there is a positive equilibrium $(I^\ast,F^\ast,M^\ast)$ whose aquatic birth rate $I^\ast(0)$ decreases in $P^\ast$, so stronger aquatic control lowers adult equilibrium abundances. Solutions can be written as

$$I(a,t)=I^\ast(a)\bigl(1+\psi_I(t-a)\bigr)e^{\eta_I(t)},\quad F(a,t)=F^\ast(a)\bigl(1+\psi_F(t-a)\bigr)e^{\eta_I(t)},\quad M(a,t)=M^\ast(a)\bigl(1+\psi_M(t-a)\bigr)e^{\eta_I(t)},$$

where $\eta_I$ is a scalar "output" coordinate and the $\psi$'s solve linear renewal (integral delay) equations driven by the normalized fecundity and emergence profiles; convergence to equilibrium is equivalent to $\eta_I\to0$ and $\psi\to0$.

**Theorem.**

1. If the internal dynamics vanish ($\psi_I\equiv0$), the feedback

$$P(t)=P^\ast+\bigl(\Gamma(t)-\Gamma^\ast\bigr)+k_I\Bigl(\frac{\Gamma^\ast\gamma^\ast}{K^\ast}-\frac{\Gamma(t)\gamma(t)}{K(t)}\Bigr)$$

makes the closed loop globally asymptotically stable, with a Lyapunov function $V_I(\eta_I)=\int_0^{\eta_I}\phi_I(s)\,ds$.
2. In general (non-trivial internal dynamics), assume (H6): with $g_F, g_I$ the normalized renewal kernels of the $\psi$-equations and $z_I = \bigl(\int_0^A a\,g_F(a)\,da\bigr)^{-1}$, $z_F = \bigl(\int_0^A a\,g_I(a)\,da\bigr)^{-1}$, there are $\kappa_I, \kappa_F > 0$ with

$$\int_0^A\Bigl|g_F(a) - z_I\kappa_I\int_a^Ag_F(s)\,ds\Bigr|\,da < 1, \qquad \int_0^A\Bigl|g_I(a) - z_F\kappa_F\int_a^Ag_I(s)\,ds\Bigr|\,da < 1.$$

   Then the system is globally asymptotically stabilizable by a uniformly bounded control that stays positive for all $t>0$ whenever the initial condition lies in the largest level set of the combined Lyapunov function $V(\eta_I,\psi_I)$ inside the admissible region.
3. (Tracking) Let $y(t) = \int_0^Aw(a)I(a,t)\,da$ be the emergent aquatic density, $p^\ast = \int_0^AI^\ast(a)\,da/y^\ast$ with $y^\ast = \int_0^Aw(a)I^\ast(a)\,da$, and $\alpha > 0$ a feedback gain. A feedforward-plus-feedback controller $P = P_{FF} + P_{FB}$ with $P_{FB} = \alpha\ln(y/y_d)$ and

$$P_{FF}(t) = \zeta_I - \frac{\partial_ty_d(t)}{y_d(t)} + \Gamma(t) - p^\ast\frac{\Gamma(t)\gamma(t)}{K(t)}\,y_d(t)$$

($\zeta_I$ the constant of the source's (3.2)), with values in a prescribed interval $(P_{\min},P_{\max})$, makes $y$ track every positive differentiable reference trajectory $y_d$ that satisfies the bound (4.9),

$$0 < y_d(t) < \frac{\min(2,\alpha)}{4p^\ast}\min\Bigl\{1,\frac{P_{\max} - P_{\min}}{2}\Bigr\},$$

and for which $P_{FF}$ takes values in $\bigl(\frac{4p^\ast}{\min(2,\alpha)}y_d(t)+P_{\min},\,P_{\max}-\frac{4p^\ast}{\min(2,\alpha)}y_d(t)\bigr)$ for all $t$ (the source's (4.11)).

## Expansion

Integrating along characteristics shows that the aquatic density at age $a$ is its birth density at time $t-a$ times a survival factor and the logistic net growth accumulated since then, which motivates the multiplicative decomposition into an equilibrium age profile, a renewal-driven shape perturbation $\psi$ and a common amplitude $e^{\eta_I}$. The amplitude obeys a scalar equation in which $P(t)$ appears additively, so the control can cancel the time variation of the logistic coefficients and inject damping proportional to $k_I$; $V_I$ is then a strict Lyapunov function for $\eta_I$. The shape perturbations satisfy linear renewal equations with kernels $g_F,g_I$ of total mass one, which converge to zero by the renewal theorem under aperiodicity, and a small-gain combination of $V_I$ with a functional of $\psi_I$ handles the coupled case while keeping $P$ positive and bounded on suitable level sets.

## Sources

- Marius Bargo, Yacouba Simporé, "Global stabilization and emergence tracking via aquatic control in an age-structured mosquito model", arXiv (2025). Section 2 (model), Section 3 (equilibrium, Remark 3.1, Lemma 3.2 on the solution representation), Section 4 (Theorems 4.1, 4.3 and 4.4), Section 5 (well-posedness, Proposition 5.1). <https://doi.org/10.48550/arXiv.2511.12289>. Published version: Nonlinear Analysis: Real World Applications 92 (2026), article 104629, <https://doi.org/10.1016/j.nonrwa.2026.104629>; locators above refer to the arXiv version.
