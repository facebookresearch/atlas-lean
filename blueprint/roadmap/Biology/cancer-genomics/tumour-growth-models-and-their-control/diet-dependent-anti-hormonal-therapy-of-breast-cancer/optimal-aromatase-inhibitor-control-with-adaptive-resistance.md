# Optimal aromatase-inhibitor control with adaptive resistance

**Extended model.** Split the tumor into estrogen-sensitive cells $S$ and resistant cells $R$, with estrogen $E$ and fat $F$. An aromatase inhibitor with time-dependent strength $u(t)$ lowers estrogen production:

$$\frac{dS}{dt} = \frac{k_1E}{a_1+E}S\big(1 - m_1(S + \eta R)\big) - \frac{ca_2^l}{a_2^l + E^l}S - \frac{ca_3^l}{a_3^l + E^l}S,$$

$$\frac{dR}{dt} = k_3R\big(1 - m_1(S + \eta R)\big) + \frac{ca_3^l}{a_3^l + E^l}S, \qquad \frac{dE}{dt} = (1-u)rF - \mu E, \qquad \frac{dF}{dt} = k_2F(1 - m_2F) - \alpha(S+R)F.$$

Sensitive cells die at low estrogen (Hill threshold $a_2$) and adapt into resistant cells (threshold $a_3$, Hill coefficient $l$, maximal rate $c$); resistant cells grow estrogen independently at rate $k_3$; $\eta$ scales competition; fat grows logistically. All parameters $k_1, k_2, k_3, a_1, a_2, a_3, m_1, m_2, c, l, \eta, r, \mu, \alpha$ are positive.

**Proposition 2.** With constant treatment ($1-u \equiv p \in (0,1]$) and non-negative initial data the solution exists, is unique, non-negative and bounded. (The source's proof of Proposition 2 also prints $\limsup_{t\to\infty}\big(S(t) + \eta R(t)\big) \le 1/m_1$ ((3.6)); this page states only the boundedness that Proposition 2 asserts, because (3.6) is deduced from the inequality (3.5), which does not hold when $S + \eta R > 1/m_1$ and drops the adaptation term, which raises $S + \eta R$ when $\eta > 1$.)

**Optimal control problem.** For bounds $0 \le u_a \le u_b < 1$, minimize over measurable $u$ with $u_a \le u \le u_b$ on $[t_{tr},t_f]$

$$\mathcal{J}(u) = \int_{t_{tr}}^{t_f}\Big(\omega_SS + \omega_RR + \frac{\omega_u}{2}u^2\Big)\,dt.$$

The source writes its control set as $u_a \le u \le u_b$ without a range; the range $0 \le u_a \le u_b < 1$ comes from its treatment parameter $p = 1 - u$, $0 < p \le 1$ (Section 3), and its computations use $u_a = 0$, $u_b = 0.99$. For $u > 1$ the estrogen equation can drive $E$ negative, where the Hill terms are undefined.

**Theorem 1 (existence).** An optimal control $u^*$ with corresponding state $(S^*,R^*,E^*,F^*)$ exists.

**Theorem 2 (optimality system).** There are adjoint variables $\lambda_1,\dots,\lambda_4$ with $\lambda_i' = -\partial\mathcal{H}/\partial x_i$ for the Hamiltonian $\mathcal{H} = \omega_SS + \omega_RR + \tfrac{\omega_u}{2}u^2 + \lambda\cdot(\text{right-hand side})$ and transversality $\lambda_i(t_f) = 0$; in particular $\lambda_3' = \dots + \mu\lambda_3$ and $\lambda_4' = -\lambda_3(1-u^*)r - \lambda_4\big(k_2 - 2k_2m_2F - \alpha(S+R)\big)$. The optimal control is the projection

$$u^* = \min\Big(u_b,\ \max\Big(u_a,\ \frac{rF\lambda_3}{\omega_u}\Big)\Big).$$

## Depends on

- [Tumor–estrogen–fat model of ER-positive breast cancer](tumor-estrogen-fat-model-of-er-positive-breast-cancer.md)

## Expansion

Boundedness: $F$ is bounded by comparison with its logistic equation and then $E$ by $E' \le rF - \mu E$; since $S + \eta R \ge S$, $S' \le \frac{k_1E}{a_1+E}S(1 - m_1S)$, so $S \le \max\{S_0, 1/m_1\}$, and then $R' \le k_3R(1 - m_1\eta R) + c\max\{S_0, 1/m_1\}$ bounds $R$. Existence (Fleming–Rishel) needs a closed convex control set, a right-hand side bounded by $C(|x| + |u|)$ on bounded states, and an integrand convex in $u$ with coercive growth, all supplied by the quadratic penalty. The control formula follows from $\partial\mathcal{H}/\partial u = \omega_uu - rF\lambda_3 = 0$ and projection onto the box; it is computed by forward–backward sweep. Because $\lambda_3$ (the shadow cost of estrogen) multiplies $F$, the optimal dose scales with the fat volume, so the optimal schedule differs between high-fat and control diets.

## Sources

- Tuğba Akman, Lisa M. Arendt, Jürgen Geisler, Vessela N. Kristensen, Arnoldo Frigessi, Alvaro Köhn-Luque, "Modeling of Mouse Experiments Suggests that Optimal Anti-Hormonal Treatment for Breast Cancer is Diet-Dependent", Bulletin of Mathematical Biology 86 (2024), 42, <https://doi.org/10.1007/s11538-023-01253-1>. Published version of arXiv:2301.10553, cited next; locators there refer to the arXiv version.
- Tuğba Akman, Lisa M. Arendt, Jürgen Geisler and Vessela N. Kristensen, *Modeling of mouse experiments suggests that optimal anti-hormonal treatment for breast cancer is diet-dependent*, arXiv:2301.10553 (2023). <https://doi.org/10.48550/arXiv.2301.10553> Section 3 (extended model, Proposition 2) and Section 4 (optimal control problem, Theorems 1 and 2).
