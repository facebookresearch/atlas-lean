# Heroin epidemic model with information-driven prevention and its reproduction-number threshold

**Model.** Let $S$ be susceptibles, $U_1$ heroin users not in treatment, $U_2$ users in treatment, $E$ individuals in preventive education, and $Z$ the density of information about the harms of heroin. With recruitment $\Lambda$, natural death rate $\mu$, initiation rate $\beta_1$ (through contact with untreated users), relapse rate $\beta_2$ of treated users through contact with untreated users, treatment-entry rate $p$, heroin-induced death rates $\delta_1, \delta_2$, rate $\theta$ of leaving education, information response $u_1 \rho S Z$, information production $a U_1 / (1 + b U_1)$ and information decay $a_0$:

$$ \dot U_1 = \beta_1 S U_1 - p U_1 + \beta_2 U_1 U_2 - (\mu + \delta_1) U_1, \qquad \dot U_2 = p U_1 - \beta_2 U_1 U_2 - (\mu + \delta_2) U_2, $$

$$ \dot S = \Lambda - \beta_1 S U_1 - \mu S + \theta E - u_1 \rho S Z, \qquad \dot E = u_1 \rho S Z - (\mu + \theta) E, \qquad \dot Z = \frac{a U_1}{1 + b U_1} - a_0 Z. $$

The region $D = \{ 0 \le S + U_1 + U_2 + E \le \Lambda/\mu,\ 0 \le Z \le a\Lambda/(a_0 \mu) \}$ is positively invariant, and the heroin-free equilibrium is $E_0 = (\Lambda/\mu, 0, 0, 0, 0)$.

**Theorem.** The basic reproduction number (next-generation matrix) is

$$ R_0 = \frac{\beta_1 \Lambda}{\mu(\mu + \delta_1 + p)}. $$

1. (Theorem 3.1) If $R_0 < 1$, $E_0$ is locally asymptotically stable.
2. (Theorem 3.2) If $\frac{\beta_1 \Lambda}{\mu(\mu + \delta_1)} < 1$, $E_0$ is globally asymptotically stable in $D$.
3. (Theorem 3.3) If $R_0 > 1$, the endemic equilibrium $E_1 = (S^*, U_1^*, U_2^*, E^*, Z^*)$ is locally asymptotically stable provided the Routh-Hurwitz conditions for the fifth-degree characteristic polynomial of the Jacobian at $E_1$ hold.

The global condition is stronger than $R_0 < 1$: it ignores the removal of users into treatment, which relapse ($\beta_2 U_1 U_2$) can partly undo.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)
- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

Only $U_1$ is an infected compartment that generates new infections: linearizing at $E_0$, new users arrive at rate $\beta_1 (\Lambda/\mu) U_1$ and leave $U_1$ at rate $(\mu + \delta_1 + p)$, so the next-generation matrix is the scalar $R_0$, and the Jacobian at $E_0$ is block triangular with eigenvalues $-\mu$, $-(\mu+\theta)$, $-a_0$, $-(\mu + \delta_2)$ and $(\mu + \delta_1 + p)(R_0 - 1)$. For global stability, the Lyapunov function $L = U_1 + U_2$ has, since the treatment and relapse terms cancel and $S \le \Lambda/\mu$ in $D$,

$$ \dot L = \beta_1 S U_1 - (\mu + \delta_1) U_1 - (\mu + \delta_2) U_2 \le (\mu + \delta_1)\Bigl[ \frac{\beta_1 \Lambda}{\mu(\mu + \delta_1)} - 1 \Bigr] U_1 - (\mu + \delta_2) U_2, $$

which is negative unless $U_1 = U_2 = 0$; LaSalle's invariance principle then gives convergence to $E_0$, because on $\{U_1 = U_2 = 0\}$ the remaining variables decay to $(\Lambda/\mu, 0, 0)$.

## Sources

- P. T. Sowndarrajan, L. Shangerganesh, A. Debbouche, D. F. M. Torres, "Optimal control of a heroin epidemic mathematical model", Optimization 71 (2022), 3107–3131, <https://doi.org/10.1080/02331934.2021.2009823>. Published version of arXiv:2111.05906, cited next; locators there refer to the arXiv version.
- Puthur Thangaraj Sowndarrajan, Lingeshwaran Shangerganesh, Amar Debbouche, Delfim F. M. Torres, "Optimal control of a heroin epidemic mathematical model", arXiv (2021). Section 2 (model, $E_0$, $R_0$), Theorems 3.1-3.3. <https://doi.org/10.48550/arXiv.2111.05906>
