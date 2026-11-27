# Optimal aromatase-inhibitor control with adaptive resistance

**Extended model.** Split the tumor into estrogen-sensitive cells $S$ and resistant cells $R$, with estrogen $E$ and fat $F$. An aromatase inhibitor with time-dependent strength $u(t)$ lowers estrogen production:

$$\frac{dS}{dt} = \frac{k_1E}{a_1+E}S\big(1 - m_1(S + \eta R)\big) - \frac{ca_2^l}{a_2^l + E^l}S - \frac{ca_3^l}{a_3^l + E^l}S,$$

$$\frac{dR}{dt} = k_3R\big(1 - m_1(S + \eta R)\big) + \frac{ca_3^l}{a_3^l + E^l}S, \qquad \frac{dE}{dt} = (1-u)rF - \mu E, \qquad \frac{dF}{dt} = k_2F(1 - m_2F) - \alpha(S+R)F.$$

Sensitive cells die at low estrogen (Hill threshold $a_2$) and adapt into resistant cells (threshold $a_3$, Hill coefficient $l$, maximal rate $c$); resistant cells grow estrogen independently at rate $k_3$; $\eta$ scales competition; fat grows logistically.

**Proposition 2.** With constant treatment ($1-u \equiv p \in (0,1]$) and non-negative initial data the solution exists, is unique, non-negative and bounded; in particular $\limsup_{t\to\infty}\big(S(t) + \eta R(t)\big) \le 1/m_1$.

**Optimal control problem.** Minimize over measurable $u$ with $u_a \le u \le u_b$ on $[t_{tr},t_f]$

$$\mathcal{J}(u) = \int_{t_{tr}}^{t_f}\Big(\omega_SS + \omega_RR + \frac{\omega_u}{2}u^2\Big)\,dt.$$

**Theorem 1 (existence).** An optimal control $u^*$ with corresponding state $(S^*,R^*,E^*,F^*)$ exists.

**Theorem 2 (optimality system).** There are adjoint variables $\lambda_1,\dots,\lambda_4$ with $\lambda_i' = -\partial\mathcal{H}/\partial x_i$ for the Hamiltonian $\mathcal{H} = \omega_SS + \omega_RR + \tfrac{\omega_u}{2}u^2 + \lambda\cdot(\text{right-hand side})$ and transversality $\lambda_i(t_f) = 0$; in particular $\lambda_3' = \dots + \mu\lambda_3$ and $\lambda_4' = -\lambda_3(1-u^*)r - \lambda_4\big(k_2 - 2k_2m_2F - \alpha(S+R)\big)$. The optimal control is the projection

$$u^* = \min\Big(u_b,\ \max\Big(u_a,\ \frac{rF\lambda_3}{\omega_u}\Big)\Big).$$

## Depends on

- [Tumor–estrogen–fat model of ER-positive breast cancer](tumor-estrogen-fat-model-of-er-positive-breast-cancer.md)

## Expansion

Boundedness uses $\frac{d}{dt}(S + \eta R) \le \max\{k_1,k_3\}(S + \eta R)\big(1 - m_1(S+\eta R)\big)$, after noting that adaptation moves mass from $S$ to $R$ and death only removes it. Existence (Fleming–Rishel) needs a closed convex control set, a right-hand side bounded by $C(|x| + |u|)$ on bounded states, and an integrand convex in $u$ with coercive growth, all supplied by the quadratic penalty. The control formula follows from $\partial\mathcal{H}/\partial u = \omega_uu - rF\lambda_3 = 0$ and projection onto the box; it is computed by forward–backward sweep. Because $\lambda_3$ (the shadow cost of estrogen) multiplies $F$, the optimal dose scales with the fat volume, so the optimal schedule differs between high-fat and control diets.

## Sources

- Tuğba Akman, Lisa M. Arendt, Jürgen Geisler, Vessela N. Kristensen, Arnoldo Frigessi, Alvaro Köhn-Luque, "Modeling of Mouse Experiments Suggests that Optimal Anti-Hormonal Treatment for Breast Cancer is Diet-Dependent", Bulletin of Mathematical Biology 86 (2024), 42, <https://doi.org/10.1007/s11538-023-01253-1>. Published version of arXiv:2301.10553, cited next; locators there refer to the arXiv version.
- Tuğba Akman, Lisa M. Arendt, Jürgen Geisler and Vessela N. Kristensen, *Modeling of mouse experiments suggests that optimal anti-hormonal treatment for breast cancer is diet-dependent*, arXiv:2301.10553 (2023). <https://doi.org/10.48550/arXiv.2301.10553> Section 3 (extended model, Proposition 2) and Section 4 (optimal control problem, Theorems 1 and 2).
