# Isoperimetric vaccine budget and optimal sex-specific vaccination

**Problem.** Control the two-sex STI vaccination model (states $S_k, V_k, I_k$ for $k = f, m$; see the control reproduction number article) with time-dependent vaccination rates $u_f(t), u_m(t)$, bounded and Lebesgue measurable with $0 \le u_k(t) \le u_{\max}$ on $[0, t_f]$. A fixed stockpile of $W$ doses, $W < N$, must be used exactly:

$$\int_0^{t_f} \bigl(u_f(t) S_f(t) + u_m(t) S_m(t)\bigr)\, dt = W \qquad \text{(isoperimetric constraint)},$$

and the objective is to minimize

$$J = \int_0^{t_f} \bigl(A_1 I_f + A_2 I_m + A_3 u_f^2 + A_4 u_m^2\bigr)\, dt, \qquad A_i > 0 .$$

**Reduction.** Introduce the cumulative-dose state $Z(t) = \int_0^t (u_f S_f + u_m S_m)\, ds$, so that

$$\dot Z = u_f S_f + u_m S_m, \qquad Z(0) = 0, \qquad Z(t_f) = W .$$

The isoperimetric problem becomes a standard problem with one fixed terminal state.

**Theorem.** Assuming some admissible control attains $Z(t_f) = W$, an optimal pair $(u_f^*, u_m^*)$ exists. If it is optimal, there are $\lambda_0 \in \{0, 1\}$ and piecewise differentiable adjoints $\lambda_1, \dots, \lambda_7$, not all zero together with $\lambda_0$, such that the optimal control minimizes the Hamiltonian

$$H = \lambda_0\bigl[A_1 I_f + A_2 I_m + A_3 u_f^2 + A_4 u_m^2\bigr] + \sum_{i=1}^{6} \lambda_i\, g_i(S, V, I, u) + \lambda_7\,(u_f S_f + u_m S_m)$$

pointwise in $u$ ($g_1, \dots, g_6$ the right-hand sides for $S_f, V_f, I_f, S_m, V_m, I_m$), the adjoints satisfy $\dot\lambda_i = -\partial H/\partial(\text{state}_i)$ with $\lambda_i(t_f) = 0$ for $i \le 6$, and $\dot\lambda_7 = 0$, so $\lambda_7 \equiv K$ is a constant with $\lambda_7(t_f)$ free. In the normal case $\lambda_0 = 1$,

$$u_f^*(t) = \min\Bigl\{\max\Bigl\{0,\ \frac{(\lambda_1 - \lambda_2 - K)\, S_f^*}{2A_3}\Bigr\},\ u_{\max}\Bigr\}, \qquad u_m^*(t) = \min\Bigl\{\max\Bigl\{0,\ \frac{(\lambda_4 - \lambda_5 - K)\, S_m^*}{2A_4}\Bigr\},\ u_{\max}\Bigr\},$$

with the constant $K$ chosen so that $Z(t_f) = W$. In the abnormal case $\lambda_0 = 0$ the Hamiltonian is linear in the controls and the optimal control is bang–bang except possibly on singular arcs (for example, vaccinate at $u_{\max}$ until the stockpile runs out), ignoring the objective.

## Depends on

- [Control reproduction number of the two-sex STI vaccination model](control-reproduction-number-of-the-two-sex-sti-vaccination-model.md)
## Expansion

The extra state $Z$ does not appear in the dynamics or the integrand, so its adjoint is constant: $K$ is the shadow price of one dose. Vaccinating a susceptible of sex $k$ moves them from $S_k$ to $V_k$ (worth $\lambda_{S_k} - \lambda_{V_k}$) and uses a dose (cost $K$); the formula sets the marginal quadratic cost $2A_k u_k$ equal to this net value times $S_k^*$, then clips to the bounds. Existence follows from the Filippov–Cesari theorem, because the integrand is convex in $u$ and the dynamics are affine in $u$. Since $Z$ has a fixed endpoint, the usual forward–backward sweep cannot be run directly; it is wrapped in an outer secant iteration on $K$ that drives $Z_K(t_f) - W$ to zero. In the numerical study, with doses for roughly 20–30% coverage, vaccinating only females was more beneficial than vaccinating both sexes; with doses for at least 40% coverage, vaccinating both sexes, at a slightly higher rate for females, was optimal.

## Sources

- F. Saldaña, V. Steindorf, A. K. Srivastav, N. Stollenwerk, M. Aguiar, "Optimal vaccine allocation for the control of sexually transmitted infections", *Journal of Mathematical Biology* 86 (2023), Eqs. (10)–(27), Theorem 2 and Section 4. <https://doi.org/10.1007/s00285-023-01910-y> (PMC10103681).
