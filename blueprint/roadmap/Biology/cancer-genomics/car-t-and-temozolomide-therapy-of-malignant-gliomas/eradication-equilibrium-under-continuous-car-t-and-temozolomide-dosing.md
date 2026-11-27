# Eradication equilibrium under continuous CAR-T and temozolomide dosing

**Model.** Let $S$ be glioma cells sensitive to both TMZ and CAR-T, $R_C$ cells resistant to CAR-T but TMZ-sensitive, $R_E$ cells resistant to TMZ but CAR-T-sensitive, $C$ CAR-T cells and $E$ the normalized TMZ efficacy. With $N=S+R_C+R_E$,

$$
\begin{aligned}
\dot S &= r_1S\Big(1-\frac{N}{K}\Big) - \alpha_1ES - \varepsilon_1ES - \alpha_2CS,\\
\dot R_C &= r_1R_C\Big(1-\frac{N}{K}\Big) - \alpha_1ER_C - \varepsilon_1ER_C,\\
\dot R_E &= r_2R_E\Big(1-\frac{N}{K}\Big) - \alpha_2CR_E + \varepsilon_1(S+R_C)E,\\
\dot C &= \bar v - \rho_1C + \frac{\rho_2SC}{g_1+S} + \frac{\rho_3R_EC}{g_2+R_E} - \rho_4\frac{NC}{g_3+C} - \alpha_3EC,\\
\dot E &= \bar E_0 - \mu E,
\end{aligned}
$$

with positive parameters. Here $\varepsilon_1$ is the TMZ-induced conversion to TMZ resistance, and $\bar v\ge 0$, $\bar E_0\ge 0$ are continuous daily doses of CAR-T cells and TMZ. Clinically, doses are impulses $E(T_1^+)=E(T_1^-)+E_0$ and $C(T_2^+)=C(T_2^-)+v$ with $\bar v=\bar E_0=0$ between them.

**Theorem.**

1. *(Positivity.)* For $\varepsilon_1\ge 0$, nonnegative initial data give nonnegative solutions; $S=0$, $R_C=0$, $R_E=0$ and $E=0$ are invariant.
2. *(No therapy: carrying-capacity plane.)* Without dosing ($\bar v=\bar E_0=0$), if $r_1\ne r_2$ every isolated biologically relevant equilibrium is unstable, while the plane $\{C=E=0,\ S+R_C+R_E=K\}$ consists of equilibria and is locally stable for the reference parameter ranges. Hence after a single dose of each therapy, trajectories approach the tumor carrying capacity.
3. *(Eradication under continuous dosing.)* With constant doses, the tumor-free state is $Q_6=(0,0,0,C^*,E^*)$ with

$$
C^* = \frac{\mu\bar v}{\alpha_3\bar E_0+\rho_1\mu},\qquad E^* = \frac{\bar E_0}{\mu},
$$

and, for the reference parameter ranges, $Q_6$ is locally asymptotically stable if and only if

$$
\bar E_0(\alpha_1+\varepsilon_1) > r_1\mu\qquad\text{and}\qquad \bar v > \frac{r_2(\bar E_0\alpha_3+\mu\rho_1)}{\mu\alpha_2}.
$$

## Expansion

The Jacobian at $Q_6$ has the real eigenvalues $-\mu$, $-(\alpha_3\bar E_0+\rho_1\mu)/\mu$, $r_1-(\alpha_1+\varepsilon_1)E^*$ (clone $R_C$), $r_1-(\alpha_1+\varepsilon_1)E^*-\alpha_2C^*$ (clone $S$) and $r_2-\alpha_2C^*$ (clone $R_E$). The two inequalities say that TMZ alone must control the CAR-T-resistant clone ($R_C$) and CAR-T alone must control the TMZ-resistant clone ($R_E$); the doubly sensitive clone is then controlled automatically. TMZ also kills CAR-T cells ($\alpha_3$), which raises the CAR-T dose needed. Without dosing, the subsystem on $C=E=0$ has first integrals $S/R_C$ and $R_E/R_C^{r_2/r_1}$, which reduces stability of each point of the carrying-capacity plane to a scalar logistic-type equation.

## Sources

- D. Sinelshchikov, J. Belmonte-Beitia, M. Italia, *A mathematical model of CAR-T cell therapy in combination with chemotherapy for malignant gliomas*, arXiv:2501.13774 (2025). <https://doi.org/10.48550/arXiv.2501.13774> — Section 2.2 (model and impulsive dosing), Section 3: Propositions 2–5 (invariant surfaces, positivity, instability of isolated equilibria, stable carrying-capacity plane), Proposition 6 (eradication criterion under continuous dosing). Published version: Chaos: An Interdisciplinary Journal of Nonlinear Science 35(6) (2025), article 063104, <https://doi.org/10.1063/5.0260252>; locators above refer to the arXiv version.
