# Global stability of an SIR model with non-monotone incidence and class-specific mortality

**Model.** Susceptible, infected and recovered fractions with births balancing deaths, $b = \mu_1 S + \mu_2 I + \mu_3 R$, and non-monotone (psychological, Xiao–Ruan) incidence $g(I) = \beta I/(1 + \alpha I^2)$, $\alpha > 0$:

$$S' = b - \mu_1 S - \frac{\beta SI}{1 + \alpha I^2}, \qquad I' = \frac{\beta SI}{1 + \alpha I^2} - (\mu_2 + \gamma)I, \qquad R' = \gamma I - \mu_3 R.$$

With the total population normalised to $1$ and $R = 1 - S - I$, this reduces to the planar system on $D = \{S, I \ge 0,\ S + I \le 1\}$

$$S' = \mu_3 + (\mu_2 - \mu_3)I - \mu_3 S - \frac{\beta SI}{1 + \alpha I^2}, \qquad I' = \frac{\beta SI}{1 + \alpha I^2} - (\mu_2 + \gamma)I.$$

**Theorem.** Let $R_0 = \beta/(\mu_2 + \gamma)$.
1. If $R_0 < 1$, the disease-free equilibrium $(1, 0)$ is globally asymptotically stable in $D$ (it is unstable if $R_0 > 1$).
2. If $R_0 > 1$, there is a unique endemic equilibrium $(S^*, I^*)$, with $S^* = (1 + \alpha I^{*2})/R_0$ and $I^* \in (0,1)$ the positive root of

$$\frac{\alpha}{R_0}I^2 + \Big(1 + \frac{\gamma}{\mu_3}\Big)I + \frac{1}{R_0} - 1 = 0,$$

and it is globally asymptotically stable in $D \setminus \{I = 0\}$. A Lyapunov function is

$$V(S,I) = \tfrac12(S - S^* + I - I^*)^2 + \frac{2\mu_3 + \gamma}{\beta}(1 + \alpha I^{*2})\Big(I - I^* - I^*\ln\frac{I}{I^*}\Big),$$

for which

$$V' = -\mu_3(S - S^*)^2 - (\mu_3 + \gamma)(I - I^*)^2 - \frac{(2\mu_3 + \gamma)\alpha S(I + I^*)}{1 + \alpha I^2}(I - I^*)^2 \le 0.$$

## Expansion

The total $S + I$ obeys the linear equation $(S + I)' = \mu_3 - \mu_3 S - (\mu_3 + \gamma)I$, which is what makes the quadratic term work: its derivative produces a cross term $-(2\mu_3 + \gamma)(S - S^*)(I - I^*)$ that exactly cancels the cross term from the Volterra part once the weight $(2\mu_3 + \gamma)(1 + \alpha I^{*2})/\beta$ is chosen and the equilibrium relations $S^*/(1 + \alpha I^{*2}) = (\mu_2 + \gamma)/\beta$ and $\mu_3 S^* + (\mu_3 + \gamma)I^* = \mu_3$ are used. The remaining term from the non-monotone incidence has a sign, because $\frac{1}{1 + \alpha I^2} - \frac{1}{1 + \alpha I^{*2}}$ has the sign of $I^* - I$, and LaSalle's principle finishes the argument. Unequal mortalities enter only through the linear part, so the threshold depends on $\mu_2$ alone. The same reduction applies to the SIRS variant with loss of immunity.

## Sources

- Y. Mohamed, A. Ahmedou and M. S. B. Elemine Vall, "Stability analysis of SIR and SIRS models with non monotone incidence function and various mortality rates", arXiv:2304.12864 (2023), Sections 2–7 (model reduction, local and global stability of the disease-free and endemic equilibria, SIRS model), <https://doi.org/10.48550/arXiv.2304.12864>.
