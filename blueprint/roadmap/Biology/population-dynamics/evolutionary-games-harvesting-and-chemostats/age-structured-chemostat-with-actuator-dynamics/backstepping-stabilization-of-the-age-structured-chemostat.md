# Backstepping stabilization of the age-structured chemostat with actuator dynamics

**Model.** Let $f(a,t) > 0$ be the age density of a microbial population in a bioreactor, ages $a \in [0,A]$, with continuous mortality $\mu \ge 0$ and fecundity $k \ge 0$ on $[0,A]$, and let the dilution rate $D(t)$ be driven through an actuator integrator with input $u(t)$:

$$
\begin{aligned}
&\partial_t f(a,t) + \partial_a f(a,t) = -\big(\mu(a) + D(t)\big) f(a,t), \qquad f(0,t) = \int_0^A k(a) f(a,t)\, da,\\
&\dot D(t) = u(t), \qquad y(t) = \int_0^A p(a) f(a,t)\, da,
\end{aligned}
$$

with $p \ge 0$ continuously differentiable and $\int_0^A p > 0$ (the measured output). The state space is $\mathcal{F} \times \mathbb{R}$, where $\mathcal{F}$ is the set of positive piecewise-$C^1$ densities satisfying the renewal condition. Assume the Lotka–Sharpe viability condition: there is $D^* > 0$ with

$$
1 = \int_0^A k(a) \exp\left(-D^* a - \int_0^a \mu(s)\, ds\right) da .
$$

Then every $f^*(a) = M \exp\left(-D^* a - \int_0^a \mu\right)$, $M > 0$, gives an equilibrium $(f^*, D^*)$; the equilibria form a continuum, so none is asymptotically stable in open loop. Fix one, with output setpoint $y^* = \int_0^A p f^* > 0$.

**Controller.** With gains $k_1, k_2 > 0$, $\tilde p = p' - p\mu$ and nominal dilution $D_{\mathrm{nom}} = D^* + k_1 \ln(y/y^*)$, the backstepping law

$$
u = -k_1 D - \frac{k_1}{y}\left[p(A) f(A,t) - p(0) f(0,t) - \int_0^A \tilde p(a) f(a,t)\, da\right] - k_2\left(D - D^* - k_1 \ln \frac{y}{y^*}\right)
$$

makes the dilution error $\delta = D - D_{\mathrm{nom}}$ satisfy $\dot\delta = -k_2 \delta$.

**Theorem (global exponential stability, unrestricted dilution).** Suppose $\tilde k(a) = k(a) f^*(a)/f^*(0)$ satisfies the technical condition: there is $\lambda > 0$ with $\int_0^A |\tilde k(a) - r\lambda \int_a^A \tilde k(s)\, ds|\, da < 1$, where $r^{-1} = \int_0^A a\tilde k(a)\, da$, and let $\sigma > 0$ be small enough that the same inequality holds with the extra factor $e^{\sigma a}$ in the integrand. Then for all $k_1, k_2 > 0$ there is $\alpha_1 \in \mathcal{K}_\infty$ such that for every initial condition $(f_0, D_0) \in \mathcal{F} \times \mathbb{R}$ the closed-loop solution exists for all $t \ge 0$ and

$$
R_1\big(f[t], D(t)\big) \le e^{-\sigma_1 t / 2}\, \alpha_1\big(R_1(f_0, D_0)\big), \qquad R_1(f,D) = \max_{a \in [0,A]} \left| \ln \frac{f(a)}{f^*(a)} \right| + |D - D^*|,
$$

with $\sigma_1 = \min(k_1/2, k_2, \sigma)$.

**Output feedback without a sensor model.** Dropping the term that needs $f(0,t)$, $f(A,t)$ and $\tilde p$ gives the implementable law $u = -(k_1 + k_2)(D - D^*) + k_1 k_2 \ln(y/y^*)$, which, under the same assumption and for every $k_1, k_2 > 0$, yields the same global estimate with some $\alpha_2 \in \mathcal{K}_\infty$ in place of $\alpha_1$ and decay rate $\sigma_1 = \min(k_1/2, k_2/2, \sigma)$. The paper also gives saturated designs that keep $D(t)$ inside a prescribed interval $(D_{\min}, D_{\max})$ with global asymptotic stability.

## Expansion

The change of variables $\eta = \ln \Pi(f)$ (a projection of $f$ on the adjoint eigenfunction of the renewal operator) and $\psi(t-a) = f(a,t)/(f^*(a)\Pi(f[t])) - 1$ splits the plant into the ODE $\dot\eta = D^* - D$ and an autonomous integral delay equation $\psi(t) = \int_0^A \tilde k(a)\psi(t-a)\, da$, whose solutions decay exponentially in a suitable functional $G$ under the technical assumption on $\tilde k$. In closed loop, $\dot\eta = -k_1\eta - \delta - k_1 v(\psi_t)$ and $\dot\delta = -k_2\delta$, where $v(\psi_t)$ is bounded by $G(\psi_t)$. A Lyapunov functional $V_1 = \frac12(\eta^2 + c_1\delta^2 + c_2 G(\psi)^2)$ satisfies $D^+ V_1 \le -\sigma_1 V_1$; translating $(\eta,\delta,\psi)$ back to $(f,D)$ gives the estimate in the logarithmic metric $R_1$, which is natural because the state must stay positive.

## Sources

- Paul‐Erik Haacker, Iasson Karafyllis, Miroslav Krstić, Mamadou Diagne, "Stabilization of age‐structured chemostat hyperbolic PDE with actuator dynamics", International Journal of Robust and Nonlinear Control 34 (2024), 6741–6763, <https://doi.org/10.1002/rnc.7181>. Published version of arXiv:2306.14078, cited next; locators there refer to the arXiv version.
- Paul-Erik Haacker, Iasson Karafyllis, Miroslav Krstić, Mamadou Diagne, "Stabilization of Age-Structured Chemostat Hyperbolic PDE with Actuator Dynamics," arXiv 2023. Section 2 (model and equilibria), Section 3 (backstepping design), Section 4, Theorem "Lyapunov stability of backstepping controller with unrestricted dilution" under the technical assumption on the birth kernel; Section 5, Theorem "Lyapunov stability of static output feedback backstepping controller with unrestricted dilution"; Sections 6–7 (constrained dilution). <https://doi.org/10.48550/arXiv.2306.14078>
