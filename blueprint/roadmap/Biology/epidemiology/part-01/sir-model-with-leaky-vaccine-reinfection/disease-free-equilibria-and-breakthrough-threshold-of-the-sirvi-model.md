# Disease-free equilibria and breakthrough threshold of the SIRVI model

**Model.** With population fractions $S, I, V, R \ge 0$, $S + I + V + R = 1$, transmission rate $\beta > 0$, vaccination rate $\nu > 0$, breakthrough (reinfection of vaccinated) rate $\alpha \ge 0$ and recovery rate $\gamma > 0$,

$$\dot S = -\beta SI - \nu S,\qquad \dot I = \beta SI + \alpha VI - \gamma I,\qquad \dot V = \nu S - \alpha VI,\qquad \dot R = \gamma I,$$

with $S(0) = 1-\eta$, $I(0) = \eta$, $V(0) = R(0) = 0$. The reproduction number is $\mathcal{R}_0 = (\beta S_0 + \alpha V_0)/\gamma$, equal to $\beta(1-\eta)/\gamma$ for these initial data.

**Results.**

1. (Equilibria.) If $\beta, \nu, \gamma > 0$, the equilibria are exactly the points with $S = I = 0$ and $V + R = 1$, $0 \le V, R \le 1$: a segment of disease-free vaccinated/removed states.
2. (Linearization.) At such a point the Jacobian has eigenvalues $0$ (twice), $-\nu$ and $\alpha V - \gamma$; the infected direction is linearly stable when $V < \gamma/\alpha$ and unstable when $V > \gamma/\alpha$. Thus a disease-free state with too large a vaccinated fraction can be reinvaded through vaccine breakthrough.
3. (Initial growth.) The epidemic initially grows, $\dot I(0) > 0$, iff $\mathcal{R}_0 > 1$.
4. (Lyapunov estimate.) For $L = \tfrac12(S+I)^2$, $\dot L = (-\nu S + \alpha VI - \gamma I)(S+I)$, which is nonpositive along any stretch of trajectory on which $\alpha V(t) \le \gamma$.

In the dimensionless time $\tau = \beta t$ the dynamics depend only on $b = \nu/\beta$, $\sigma = \alpha/\beta$ and $k = \gamma/\beta$.

## Expansion

Setting $\dot S = 0$ with $\nu > 0$ forces $S(\beta I + \nu) = 0$, so $S = 0$; then $\dot V = -\alpha VI = 0$ and $\dot R = \gamma I = 0$ force $I = 0$, and conservation gives $V + R = 1$. At $S = I = 0$ the Jacobian is block triangular with diagonal entries $-\nu$ (from $S$), $\alpha V + \beta S - \gamma = \alpha V - \gamma$ (from $I$) and zeros for $V$ and $R$, reflecting the continuum of equilibria. Because $\dot S \le -\nu S$, $S(t) \le S_0e^{-\nu t} \to 0$, so in the long run new infections come only from vaccine breakthrough; with full protection ($\alpha = 0$) the model reduces to an SIR model with vaccination.

## Depends on

- [Basic reproduction number](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Sources

- Turkyilmazoglu M, "An extended epidemic model with vaccination: Weak-immune SIRVI", Physica A (2022), Section 2, Eqs. (1)–(3); Section 3, Theorems 1–3, Eqs. (4)–(9); Section 4, Eqs. (10)–(11) and Corollary, <https://doi.org/10.1016/j.physa.2022.127429>, PMCID PMC9033298.
