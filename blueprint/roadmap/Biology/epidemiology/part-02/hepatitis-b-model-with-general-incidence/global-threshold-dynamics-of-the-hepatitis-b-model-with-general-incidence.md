# Global threshold dynamics of the hepatitis B model with general incidence

Consider

$$

\begin{aligned}
S' &= \Lambda - f(S,I) - (\mu_0 + \nu)S,\\
I' &= f(S,I) - (\mu_0 + \mu_1 + \beta)I,\\
R' &= \beta I + \nu S - \mu_0 R,
\end{aligned}

$$

with recruitment $\Lambda$, natural mortality $\mu_0$, disease mortality $\mu_1$, recovery rate $\beta$, vaccination rate $\nu$ (all positive), and an incidence function $f$ satisfying:

- (H1) $f : \mathbb{R}_+^2 \to \mathbb{R}_+$ is differentiable, $f(S,0) = f(0,I) = 0$, and $f > 0$ for $S,I > 0$;
- (H2) $f(S,I) \le \eta S$ for some $\eta > 0$;
- (H3) $\partial_S f > 0$ and bounded for $S \ge 0$, $I > 0$;
- (H4) $\partial_I f \ge 0$;
- (H5) $I\,\partial_I f(S,I) - f(S,I) \le 0$.

**Theorem.** $\mathbb{R}_+^3$ is positively invariant and solutions are ultimately bounded. The disease-free equilibrium is $E^0 = \big(\tfrac{\Lambda}{\mu_0+\nu},\,0,\,\tfrac{\nu\Lambda}{\mu_0(\mu_0+\nu)}\big)$ and

$$

\mathcal R_0 = \frac{1}{\mu_0 + \mu_1 + \beta}\;\frac{\partial f}{\partial I}\Big(\frac{\Lambda}{\mu_0+\nu},\,0\Big).

$$

1. If $\mathcal R_0 \le 1$, $E^0$ is globally asymptotically stable.
2. A positive (endemic) equilibrium exists iff $\mathcal R_0 > 1$; it is then unique, $E^* = (S^*,I^*,R^*)$ with $I^*$ the unique positive root of $f\big(\tfrac{\Lambda - (\mu_0+\mu_1+\beta)I}{\mu_0+\nu}, I\big) = (\mu_0+\mu_1+\beta)I$, $S^* = \tfrac{\Lambda - (\mu_0+\mu_1+\beta)I^*}{\mu_0+\nu}$, $R^* = \tfrac{\beta I^* + \nu S^*}{\mu_0}$; and $E^*$ is globally asymptotically stable for all initial data with $I(0) > 0$.

## Expansion

Since $R$ does not feed back, it suffices to study the planar $(S,I)$ system. For $\mathcal R_0 \le 1$ the Lyapunov function $V(S) + I$, with $V(S) = S - S_0 - \int_{S_0}^S f(S_0,I)/f(\tau,I)\,d\tau$, works because (H5) makes $f(S,I)/I$ non-increasing in $I$, so $f(S_0,I) \le \partial_I f(S_0,0)\,I$. For $\mathcal R_0 > 1$ the Bendixson–Dulac criterion with multiplier $1/I$ rules out periodic orbits in the positive quadrant, the disease-free equilibrium is a saddle repelling the interior, and Poincaré–Bendixson gives global convergence to $E^*$.

## Sources

- Manh Tuan Hoang, "Dynamical analysis of a generalized hepatitis B epidemic model and its dynamically consistent discrete model", arXiv (2021). Section 2 (Propositions 1–2, Theorems 1–3). <https://doi.org/10.48550/arXiv.2112.06284>. Published version: Mathematics and Computers in Simulation 205 (2023), 291–314, <https://doi.org/10.1016/j.matcom.2022.10.006>; locators above refer to the arXiv version.
