# Threshold dynamics of the SIRS model with immune boosting and delays

**Model.** In a normalized population ($S + I + R = 1$) with equal birth and death rate $d\ge0$, susceptibles are infected at rate $\beta I$, infectives recover at rate $\gamma > 0$, immunity lasts $\tau > 0$, and an immune host exposed to infection at rate $\nu\beta I$ ($\nu\ge0$ the boosting strength) has its immunity fully restored for another $\tau$. Hosts losing immunity at time $t$ either recovered at $t-\tau$ or were boosted at $t-\tau$, and were neither boosted nor dead since, which gives

$$S'(t) = d(1 - S(t)) - \beta I(t)S(t) + I(t-\tau)\big(\gamma + \nu\beta(1 - S(t-\tau) - I(t-\tau))\big)\exp\Big(-d\tau - \nu\beta\int_{-\tau}^0I(t+u)\,du\Big),$$

$$I'(t) = \beta I(t)S(t) - (\gamma + d)I(t),$$

with nonnegative initial functions on $[-\tau,0]$ satisfying $S + I\le1$. The basic reproduction number is

$$\mathcal R_0 = \frac{\beta}{d + \gamma}.$$

**Theorem.**

1. (Well-posedness.) The system has a unique global solution, and an explicit subset of initial histories (those consistent with $R\ge0$ along the past immunity window) is forward invariant, so $S, I, R\ge0$.
2. (Disease-free threshold.) If $\mathcal R_0\le1$, the disease-free equilibrium $(1,0)$ is the only equilibrium and is globally asymptotically stable on that set.
3. (Endemic equilibrium and persistence.) If $\mathcal R_0 > 1$, there is a unique endemic equilibrium $(1/\mathcal R_0, I^\ast)$ with $I^\ast > 0$, and the disease is uniformly persistent: there is $\delta > 0$ with $\liminf_{t\to\infty}I(t)\ge\delta$ for every solution with $I > 0$ initially.
4. (No immunity, $\tau = 0$.) The limiting SIS system has the same $\mathcal R_0$; the disease-free equilibrium is globally asymptotically stable if $\mathcal R_0\le1$, and the unique endemic equilibrium is globally asymptotically stable off the disease-free line if $\mathcal R_0 > 1$.
5. (Characteristic roots.) Any characteristic root $\lambda$ of the linearization at the endemic equilibrium with $\Re\lambda > 0$ satisfies $|\lambda|\le\max\{1,\hat a + \hat b + \hat c\}$ with $\hat a = d + \beta(\nu+1)$, $\hat b = \beta(\gamma + \beta(2\nu+1))$, $\hat c = 2\nu\beta^2(\gamma + \nu\beta)$, which localizes the roots for a continuation analysis in $\tau$.

Numerically, with boosting the endemic equilibrium undergoes multiple stability switches (Hopf bifurcations giving sustained oscillations, and restabilizations) as $\tau$ increases.

## Expansion

Equilibria satisfy $\beta S^\ast = \gamma + d$, so $S^\ast = 1/\mathcal R_0$, and substituting into the $S$-equation gives a scalar equation for $I^\ast$ whose two sides (a line and a convex curve in $I^\ast$) meet exactly once in $(0,1]$ when $\mathcal R_0 > 1$. For $\mathcal R_0\le1$, $I' \le (\beta - \gamma - d)I \le 0$ since $S\le1$, and a LaSalle-type argument for the delay system yields global convergence. Persistence follows from the general theory of uniform persistence for semiflows, using that the disease-free set repels when $\mathcal R_0 > 1$. Local stability of the endemic equilibrium is decided by a transcendental characteristic equation in $\lambda$ and $\tau$; the root bound confines unstable roots to a compact region, where roots crossing the imaginary axis are tracked numerically.

## Sources

- Maria Vittoria Barbarossa, Monika Polner, Gergely Röst, "Stability switches induced by immune system boosting in an SIRS model with discrete and distributed delays", arXiv (2016). Section 2 (model), Theorem 3.1, Section 4 (basic reproduction number, Theorem 4.1, Proposition 1, Theorem 4.2), Section 5 (Propositions 3–4), Section 6 (Proposition 5, stability switches). <https://doi.org/10.48550/arXiv.1606.03962>. Published version: SIAM Journal on Applied Mathematics 77(3) (2017), 905–923, <https://doi.org/10.1137/16m1077234>; locators above refer to the arXiv version.
