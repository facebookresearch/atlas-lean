# Bistability for risk-tolerators and a damped endemic focus for risk-averters in the actSIS model

**Model.** In the actively controlled SIS (actSIS) model, the infected fraction $p\in[0,1]$ evolves with an infection rate $\bar\beta\alpha(p_s)$. Here $\bar\beta$ is the intrinsic transmission rate and $\alpha(p_s)\in[0,1]$ is an effective contact rate that individuals adjust using a delayed, low-pass-filtered observation $p_s$ of the infection level:

$$\dot p = \bar\beta\,\alpha(p_s)(1-p)p - \delta p,\qquad \tau_s\dot p_s = -p_s + p .$$

Let $\phi(p;\mu,\nu) = \big(1 + (p(1-\mu)/(\mu(1-p)))^{-\nu}\big)^{-1}$ be an increasing sigmoid on $[0,1]$ with $\phi(\mu) = 1/2$ and slope parameter $\nu$. **Risk-tolerators** use $\alpha = \phi^T := \phi(\cdot;\mu_T,\nu_T)$: they make more contacts as prevalence rises. **Risk-averters** use $\alpha = 1 - \phi^A$ with $\phi^A := \phi(\cdot;\mu_A,\nu_A)$: they reduce contacts as prevalence rises.

**Theorem (risk-tolerators).** With $\alpha = \phi^T$:

1. The infection-free equilibrium $p = p_s = 0$ is always stable.
2. Endemic equilibria $p = p_s = p^*$ solve $\phi^T(p^*)(1-p^*) = \delta/\bar\beta$. There are zero, one or two of them, and such an equilibrium is stable if $\phi^{T\prime}(p^*)(1-p^*)^2 < \delta/\bar\beta$.
3. A saddle-node bifurcation at $(\bar\beta_c, p^*)$ creates a stable upper branch and an unstable lower branch, with $\bar\beta_c/\delta > 1$. The epidemic threshold is therefore larger than that of the uncontrolled SIS model.
4. For $\bar\beta > \bar\beta_c$ the infection-free and endemic states are bistable. For $\bar\beta \le \bar\beta_c$ the infection-free state is the only stable equilibrium.

**Theorem (risk-averters).** With $\alpha = 1 - \phi^A$:

1. The infection-free equilibrium is stable if $\bar\beta < \delta$. The endemic equilibrium, solving $(1-\phi^A(p^*))(1-p^*) = \delta/\bar\beta$, exists exactly when $\bar\beta > \delta$ and is then always stable, so the bifurcation is transcritical as in the SIS model.
2. Let $a = \delta p^*/(1-p^*)$, $b = \frac{1-p^*}{1-\phi^A(p^*)}\phi^{A\prime}(p^*)$ and $c = 1/\tau_s$. The endemic equilibrium is a stable focus, with oscillatory overshoot, if $b > (a-c)^2/(4ac)$.
3. The endemic level satisfies $p^* < 1 - \delta/\bar\beta$, the SIS endemic level.

In a two-group population mixing risk-averters with other types, the endemic equilibrium can lose stability through a Hopf bifurcation, which produces sustained epidemic waves under active control.

## Expansion

Equilibria satisfy $p = p_s$ and $\bar\beta\alpha(p)(1-p) = \delta$. At an endemic state the Jacobian of the planar system has trace $-a-c$ and determinant $c\,\frac{p^*}{1-p^*}\big(\delta - \bar\beta\alpha'(p^*)(1-p^*)^2\big)$, which for risk-averters equals $ac(1+b)$. For tolerators, $\alpha(0) = 0$ makes $p = 0$ stable regardless of $\bar\beta$. The hump-shaped curve $\phi^T(p)(1-p)$ produces the fold. For averters, $\alpha' < 0$ makes the determinant positive whenever the endemic state exists. The discriminant condition $(a+c)^2 < 4ac(1+b)$ gives complex eigenvalues, which is exactly $b > (a-c)^2/(4ac)$. With heterogeneous groups the state space is four-dimensional, and the Guckenheimer–Holmes conditions (non-hyperbolicity, transversality, nondegeneracy) give the Hopf bifurcation.

## Proof depends on

- [Routh–Hurwitz: a real 2 × 2 matrix is Hurwitz iff tr M < 0 < det M](../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-hurwitz-iff-trace-neg-and-det-pos.md)
- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)
- [Lyapunov's indirect method, instability](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)

## Sources

- Y. Zhou, S. A. Levin and N. E. Leonard, "Active Control and Sustained Oscillations in actSIS Epidemic Dynamics", arXiv:2007.01424 (2020), Section 3 (Theorems 3.1 and 3.2) and Section 4 (Theorem 4.1 and Proposition 4.2), <https://doi.org/10.48550/arXiv.2007.01424>.
