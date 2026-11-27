# Equilibria and thresholds of the zebra–carcass–scavenger anthrax model

**Model.** Let $z$ be living zebras, $u$ carcasses from natural death, $c$ anthrax carcasses and $j$ scavengers, with positive parameters $r, K, \mu, a, \rho, \alpha, b, d$:

$$z' = rz\Big(1 - \frac{z}{K}\Big) - \mu z - acz,\qquad u' = \mu z - \rho u - \alpha ju,\qquad c' = acz - \rho c - \alpha jc,\qquad j' = bj(u+c) - dj.$$

Put $m = \mu/r$ and

$$R_Z = \frac{aK(1-m)}{\rho},\qquad R_J = \frac{ad}{b\mu},\qquad D(E_1) = \frac{b\mu K(1-m)}{\rho d},\qquad D(E_3) = \frac{br}{ad}\Big(1 - \frac{\rho}{aK}\Big).$$

$R_Z$ is the anthrax reproduction number without scavengers, $R_J$ the one with scavengers at their anthrax-free equilibrium, and $D(E_1)$, $D(E_3)$ are the scavenger demographic reproduction numbers without and with anthrax.

**Equilibria and local stability** (assuming $m < 1$; if $m > 1$ only the extinction state $E_0 = 0$ exists and it is stable):

| equilibrium | $(z^*, u^*, c^*, j^*)$ | exists if | locally asymptotically stable if |
|---|---|---|---|
| $E_1$: no anthrax, no scavengers | $\big(K(1-m),\ \tfrac{\mu}{\rho}K(1-m),\ 0,\ 0\big)$ | always | $R_Z < 1$ and $D(E_1) < 1$ |
| $E_2$: scavengers, no anthrax | $\big(K(1-m),\ \tfrac{d}{b},\ 0,\ \tfrac{1}{\alpha}(\tfrac{b\mu}{d}K(1-m) - \rho)\big)$ | $D(E_1) > 1$ | $R_J < 1$ |
| $E_3$: anthrax, no scavengers | $\big(\tfrac{\rho}{a},\ \tfrac{\mu}{a},\ \tfrac{r}{aK}(K(1-m) - \tfrac{\rho}{a}),\ 0\big)$ | $R_Z > 1$ | $D(E_3) < 1$ |
| $E_4$: anthrax and scavengers | $\big(K(1-\tfrac{ad}{br}),\ \tfrac{\mu}{a},\ \tfrac{d}{b} - \tfrac{\mu}{a},\ \tfrac{a}{\alpha}K(1-\tfrac{ad}{br}) - \tfrac{\rho}{\alpha}\big)$ | $D(E_3) > 1$ and $R_J > 1$ | whenever it exists |

Moreover $D(E_1) > 1 \iff R_Z > R_J$, and $D(E_3) > 1 \iff mR_J + (1-m)/R_Z < 1$. Anthrax persists only if both $R_Z > 1$ and $R_J > 1$, so the anthrax threshold is $\min(R_Z, R_J) > 1$; this minimum is the reproduction number at the disease-free equilibrium that is stable without anthrax ($E_2$, with value $R_J$, when $R_J < R_Z$, and $E_1$, with value $R_Z$, otherwise). The source writes this threshold as $R_0 = \max(R_Z, R_J)$, which does not match its own persistence condition. Scavengers hurt anthrax exactly when they can persist without it. If $R_Z < 1$ and $D(E_1) < 1$, $E_1$ attracts all solutions.

## Expansion

At $E_2$ the Jacobian has eigenvalues $z^*a - b\mu/d$ and $\mu - r$, and a $2\times2$ block with negative trace and determinant of the sign of $b\mu z^* - \rho d$, giving stability iff $R_J < 1$. At $E_3$ the scavenger growth rate is $b(u^* + c^*) - d$, whose sign is that of $D(E_3) - 1$. The equivalences follow by clearing denominators, e.g. $R_Z > R_J \iff b\mu K(1-m) > \rho d$. Global stability of $E_1$ follows by comparison: $\limsup z \le K(1-m)$, then $c \to 0$ when $R_Z < 1$ and $j \to 0$ when $D(E_1) < 1$, after which the remaining zebra–carcass system converges.

## Depends on

- [Basic reproduction number](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Logistic growth](../../../population-dynamics/logistic-growth-equation/logistic.md)

## Sources

- Mackey C, Kribs C, "Can scavengers save zebras from anthrax? A modeling study", Infect Dis Model (2021), Section 2, Eqs. (1)–(4); Section 3, Eqs. (5)–(9), Tables 2–3 and Section 3.4.3; Section 4, <https://doi.org/10.1016/j.idm.2020.10.016>, PMCID PMC7708949.
