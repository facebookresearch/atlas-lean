# Reproduction number of an SIR model with two behavioral susceptible classes

**Model.** A population of size $N$ is split into two susceptible classes with different contact behavior (for example, people who do and do not follow mitigation measures), with transmission rates $\beta_1 > \beta_2 > 0$. Infections are symptomatic ($I_s$) with probability $\lambda$ and asymptomatic ($I_a$) otherwise; asymptomatic cases become symptomatic at rate $\gamma$, and all infected recover at rate $\kappa$:

$$\begin{aligned}
\dot S_1 &= -\beta_1\tfrac{S_1}{N}(I_a + I_s), \qquad \dot S_2 = -\beta_2\tfrac{S_2}{N}(I_a + I_s),\\
\dot I_s &= \lambda\Big[\beta_1\tfrac{S_1}{N} + \beta_2\tfrac{S_2}{N}\Big]\,(I_a + I_s) + \gamma I_a - \kappa I_s,\\
\dot I_a &= (1-\lambda)\Big[\beta_1\tfrac{S_1}{N} + \beta_2\tfrac{S_2}{N}\Big]\,(I_a + I_s) - (\gamma + \kappa)I_a, \qquad \dot R = \kappa(I_a + I_s).
\end{aligned}$$

Disease-free equilibria are $(\rho N, (1-\rho)N, 0, 0, 0)$, $\rho \in (0,1)$ being the fraction in the higher-contact class.

**Theorem.**

1. The basic reproduction number at such an equilibrium is

    $$R_0 = \frac{\rho\beta_1 + (1-\rho)\beta_2}{\kappa},$$

    and the Jacobian of the linearized infected subsystem $(I_s, I_a)$ at $(\rho N, (1-\rho)N, 0, 0, 0)$ is Hurwitz if and only if $\rho\beta_1 + (1-\rho)\beta_2 < \kappa$, i.e. $R_0 < 1$. Below, the disease-free equilibrium is called *linearly stable* when this Jacobian is Hurwitz and *linearly unstable* when it has an eigenvalue with positive real part.

2. If $\beta_2 \ge \kappa$, the disease-free equilibrium is linearly unstable for every $\rho$. If $\beta_2 < \min\{\beta_1, \kappa\}$, it is linearly stable exactly when $\rho < (\kappa - \beta_2)/(\beta_1 - \beta_2)$; in particular, if $\beta_1 < \kappa$ it is linearly stable for every $\rho \in (0,1)$.
3. The normalized sensitivity indices of $R_0$ are ordered by $\rho$: $\Upsilon^{R_0}_\rho < \Upsilon^{R_0}_{\beta_1} < \Upsilon^{R_0}_{\beta_2}$ if $\rho < \frac{\beta_2}{\beta_1+\beta_2}$; $\Upsilon^{R_0}_\rho < \Upsilon^{R_0}_{\beta_2} < \Upsilon^{R_0}_{\beta_1}$ if $\frac{\beta_2}{\beta_1+\beta_2} < \rho < \frac{\beta_2}{\beta_1}$; and $\Upsilon^{R_0}_{\beta_2} < \Upsilon^{R_0}_\rho < \Upsilon^{R_0}_{\beta_1}$ if $\rho > \frac{\beta_2}{\beta_1}$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

Every infected individual, symptomatic or not, recovers at the same rate $\kappa$ and transmits at the population-averaged rate $B_\rho = \rho\beta_1 + (1-\rho)\beta_2$; the transition from asymptomatic to symptomatic only relabels infecteds. The next-generation matrix therefore has spectral radius $B_\rho/\kappa$, independent of $\lambda$ and $\gamma$. The threshold is linear in the behavioral mix $\rho$, so the critical compliance level is the point where the averaged contact rate equals the recovery rate; sensitivity analysis says which lever (behavior mix or either contact rate) matters most in each regime.

## Sources

- Robert F. Allen, Katherine Heller and Matthew A. Pons, "Analysis of SIR Epidemic Models with Sociological Phenomenon", SPORA: A Journal of Biomathematics 8 (2022), <https://doi.org/10.30707/spora8.1.1647886301.837479>; numbering as in arXiv:2207.08999: Theorems 2.1, 2.2, 2.3, 2.6 and 2.7.
