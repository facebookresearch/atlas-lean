# Global stability of the SAIRS model with asymptomatic transmission and vaccination

**Model.** In a population normalized to $S + A + I + R = 1$, susceptibles are infected by asymptomatic ($A$) and symptomatic ($I$) individuals, enter the asymptomatic class, develop symptoms at rate $\alpha$ or recover at rate $\delta_A$; symptomatic individuals recover at rate $\delta_I$; susceptibles are vaccinated at rate $\nu$; immunity (natural or vaccine-induced) wanes at rate $\gamma$; births and deaths occur at rate $\mu$:

$$\begin{aligned} S' &= \mu - (\beta_A A + \beta_I I)S - (\mu + \nu)S + \gamma R, \\ A' &= (\beta_A A + \beta_I I)S - (\alpha + \delta_A + \mu)A, \\ I' &= \alpha A - (\delta_I + \mu)I, \\ R' &= \delta_A A + \delta_I I + \nu S - (\gamma + \mu)R. \end{aligned}$$

The basic reproduction number is

$$\mathcal R_0 = \Big(\beta_A + \frac{\alpha\beta_I}{\delta_I + \mu}\Big)\frac{\gamma + \mu}{(\alpha + \delta_A + \mu)(\nu + \gamma + \mu)}.$$

**Theorem.**

1. The simplex is positively invariant. The disease-free equilibrium $x_0 = \big(\frac{\gamma+\mu}{\nu+\gamma+\mu}, 0, 0, \frac{\nu}{\nu+\gamma+\mu}\big)$ is globally asymptotically stable if $\mathcal R_0 < 1$ and unstable if $\mathcal R_0 > 1$; without vaccination ($\nu = 0$) it is globally asymptotically stable also for $\mathcal R_0 = 1$.
2. If $\mathcal R_0 > 1$ the system is uniformly persistent, has a unique endemic equilibrium $x^*$ in the interior, and $x^*$ is locally asymptotically stable.
3. $x^*$ is globally asymptotically stable in the interior when $\mathcal R_0 > 1$ in each of the following cases:
   - no loss of immunity ($\gamma = 0$, the SAIR model with vaccination, for which $\mathcal R_0 = (\beta_A + \frac{\alpha\beta_I}{\delta_I + \mu})\frac{\mu}{(\alpha + \delta_A + \mu)(\nu + \mu)}$);
   - equal transmission and recovery rates, $\beta_A = \beta_I$ and $\delta_A = \delta_I$;
   - $\beta_A < \delta_I$.

The SAIR case settles an open problem on the global stability of the endemic equilibrium of the SAIR model posed by Ansumali et al. (2020).

## Expansion

$\mathcal R_0$ is the spectral radius of the next-generation matrix for $(A, I)$ at $x_0$: an asymptomatic infective causes $\beta_A/(\alpha + \delta_A + \mu)$ infections directly and $\frac{\alpha}{\alpha+\delta_A+\mu}\cdot\frac{\beta_I}{\delta_I+\mu}$ through the symptomatic stage, scaled by the susceptible fraction at $x_0$. Global attractivity of $x_0$ for $\mathcal R_0 < 1$ and of $x^*$ in the SAIR and equal-rate cases are proved with Lyapunov functions and LaSalle's invariance principle, and uniform persistence follows from persistence theory for the boundary flow. The case $\beta_A < \delta_I$ uses the geometric approach of Li–Muldowney and Lu–Lu: a Lozinskii measure of the second additive compound of the Jacobian is shown to be negative along trajectories, which rules out periodic, homoclinic and heteroclinic orbits.

## Sources

- Stefania Ottaviano, Mattia Sensi, Sara Sottile, "Global stability of SAIRS epidemic models", arXiv (2021). Section 2 (model, Lemma 2 for $\mathcal R_0$), Theorems 1, 4, 5, 8, 10, 11, 12, 13, 14 and 16. <https://doi.org/10.48550/arXiv.2109.05122>. Published version: Nonlinear Analysis: Real World Applications 65 (2022), article 103501, <https://doi.org/10.1016/j.nonrwa.2021.103501>; locators above refer to the arXiv version.
