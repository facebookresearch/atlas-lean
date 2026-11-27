# Time-since-immunization SIR model with several vaccines

**Model.** Immunity acquired by recovery or by vaccination is structured by the time $\tau$ elapsed since it was acquired. Let $S(t)$ and $I(t)$ be the susceptible and infected populations. Let $R(t,\tau)$ be the density of individuals at time $t$ who recovered at time $t - \tau$, for $\tau \in [0, T_R]$, and let $V_j(t,\tau)$ be the density of those dosed with vaccine $j$ at time $t - \tau$, for $\tau \in [0, T_j]$ and $j = 1,\dots,m$. Vaccine $j$ is administered at rate $p_j(t, S, V, I, R) \ge 0$ (the control). Then

$$\begin{aligned} \dot S &= -\rho_S\,I\,S + R(t,T_R) + \sum_{j=1}^m V_j(t,T_j) - \sum_{j=1}^m p_j,\\ \dot I &= \Bigl(\rho_S\,S + \int_0^{T_R}\rho_R(\tau)R(t,\tau)\,d\tau + \sum_{j=1}^m\int_0^{T_j}\rho_j(\tau)V_j(t,\tau)\,d\tau\Bigr)I - \theta I - \mu I,\\ \partial_tR + \partial_\tau R &= -\rho_R(\tau)\,R\,I, \qquad R(t,0) = \theta I,\\ \partial_tV_j + \partial_\tau V_j &= -\rho_j(\tau)\,V_j\,I, \qquad V_j(t,0) = p_j . \end{aligned}$$

Here $\rho_S$ is the infectivity for susceptibles, $\theta$ the recovery rate and $\mu$ the disease mortality. The functions $\rho_R(\tau)$ and $\rho_j(\tau)$ give the residual susceptibility at time $\tau$ after recovery or after a dose of vaccine $j$. Individuals return to $S$ when their immunity window ends ($\tau = T_R$ or $\tau = T_j$). A typical choice is

$$\rho_R(\tau) = \rho_R^- + (\rho_S - \rho_R^-)\,\Phi(\tau/T_R), \qquad \Phi(s) = (4 - 3s)s^3,$$

which rises continuously and monotonically from the small post-recovery value $\rho_R^-$ to $\rho_S$. The vaccine profiles $\rho_j$ can encode a delay before protection starts and a vaccine-specific level and duration of protection.

**Properties.**

1. (Mass balance.) Population changes only through disease deaths:

$$\frac{d}{dt}\Bigl(S + I + \int_0^{T_R}R(t,\tau)\,d\tau + \sum_{j=1}^m\int_0^{T_j}V_j(t,\tau)\,d\tau\Bigr) = -\mu I .$$

2. (Reductions.) With $T_R = \infty$, $\rho_R \equiv 0$ and no vaccination, the system reduces to the classical SIR model $\dot S = -\rho_SIS$, $\dot I = \rho_SIS - (\theta + \mu)I$. Each finite $T_R$ or $T_j$ adds a delayed return flux into $S$.
3. (Age structure.) The framework extends to a continuous host age $a$, or to finitely many age classes, by letting all rates, immunity windows $T_R(a)$, $T_j(a)$ and dosing controls depend on $a$, with ageing transport $\partial_a$ added to every equation.

Comparing vaccination strategies, such as which vaccine to dose to which age class and when, is then an optimal control problem over the rates $p_j$, subject to supply constraints.

## Expansion

Each immune compartment is a McKendrick-type transport equation in the time-since-immunization variable. Its inflow at $\tau = 0$ is the recovery or dosing rate, its loss along characteristics is reinfection at rate $\rho(\tau)I$, and its outflow at the end of the window feeds $S$. Integrating each transport equation over $\tau$ and adding all equations makes the boundary fluxes and infection terms cancel pairwise, which leaves only $-\mu I$. Solving along characteristics, $V_j(t,\tau) = p_j(t-\tau)\exp\bigl(-\int_0^\tau\rho_j(s)I(t-\tau+s)\,ds\bigr)$, turns the system into a delay–integral system for $(S, I)$, which is what the numerical schemes integrate.

## Sources

- Rinaldo M. Colombo, Mauro Garavello, "Infectious Diseases Spreading Fought by Multiple Vaccines Having a Prescribed Time Effect", arXiv (2021). Section 2 (single vaccine: the SIR model, the recovery-age model and its conservation law, choice of $\rho_R$), Section 3 (concurrent vaccines), Section 4 (continuous and discrete age structures). <https://doi.org/10.48550/arXiv.2112.14626>. Published version: Acta Biotheoretica 71(1) (2023), article 1, <https://doi.org/10.1007/s10441-022-09452-4>; locators above refer to the arXiv version.
