# Competitive reproduction numbers of a two-strain SIR model with vaccination

**Model (integrated immunity).** A population of size $N$ is split into susceptibles $S$, individuals infectious with strain 1 ($I_1$, more transmissible, blocked by immunity) or strain 2 ($I_2$, immune-resistant), and partially immune individuals $R$ (protected against strain 1 only):

$$\begin{aligned}
\dot S &= -\tfrac{\beta_1}{N}SI_1 - \tfrac{\beta_2}{N}SI_2 - \lambda S + \alpha R, & \dot I_1 &= \tfrac{\beta_1}{N}SI_1 - \gamma I_1,\\
\dot I_2 &= \tfrac{\beta_2}{N}(S + R)I_2 - \gamma I_2, & \dot R &= \gamma(I_1 + I_2) - \tfrac{\beta_2}{N}RI_2 + \lambda S - \alpha R,
\end{aligned}$$

with vaccination rate $\lambda$, recovery rate $\gamma$ and immunity loss rate $\alpha$.

**Result.** The strain-specific basic reproduction numbers and the competitive (invasion) reproduction numbers are

$$\mathcal R_1 = \frac{\beta_1}{\gamma}\cdot\frac{\alpha}{\alpha + \lambda}, \qquad \mathcal R_2 = \frac{\beta_2}{\gamma}, \qquad \mathcal R_0 = \max\{\mathcal R_1, \mathcal R_2\},$$

$$\mathcal R_{12} = \frac{\beta_1}{\beta_2}\cdot\frac{\alpha}{\alpha + \beta_2 + \lambda - \gamma}, \qquad \mathcal R_{21} = \frac{\beta_2}{\beta_1}\cdot\frac{\beta_1 + \alpha + \lambda}{\gamma + \alpha},$$

where $\mathcal R_{12}$ is the reproduction number of strain 1 invading the strain-2-only equilibrium and $\mathcal R_{21}$ that of strain 2 invading the strain-1-only equilibrium. The model shows disease-free behaviour if $\mathcal R_0 < 1$; strain-1-only behaviour if $\mathcal R_1 > 1 > \mathcal R_2$, or $\mathcal R_1, \mathcal R_2, \mathcal R_{12} > 1 > \mathcal R_{21}$; strain-2-only behaviour symmetrically; and coexistence if all four exceed $1$. Vaccination lowers $\mathcal R_1$ and $\mathcal R_{12}$ and raises $\mathcal R_{21}$, so increasing $\lambda$ shifts the competitive advantage to the immune-resistant strain.

With waning immunity of Erlang ($\mathrm{Gamma}(k, k\alpha)$) duration and partial resistance, the distributed-delay versions of the model are equivalent, by the linear chain trick, to ODE systems with $k$ chained immune classes.

## Expansion

At the disease-free state $S/N = \alpha/(\alpha + \lambda)$, giving $\mathcal R_1$; strain 2 infects both $S$ and $R$, so $\mathcal R_2 = \beta_2/\gamma$. At the strain-2 equilibrium $(S + R)/N = \gamma/\beta_2$, and balancing the $S$-equation gives $S/N = \alpha\gamma/(\beta_2(\alpha + \beta_2 + \lambda - \gamma))$, whence $\mathcal R_{12} = \beta_1 S/(N\gamma)$; $\mathcal R_{21}$ follows the same way from the strain-1 equilibrium. Crossing $\mathcal R_i = 1$ destabilizes the corresponding equilibrium but does not by itself prove stability of another one.

## Sources

- Matthew D. Johnston, Bruce Pell, Jared Pemberton and David A. Rubel, "The Effect of Vaccination on the Competitive Advantage of Two Strains of an Infectious Disease", Bulletin of Mathematical Biology 87 (2025), 19, <https://doi.org/10.1007/s11538-024-01378-x>; numbering as in arXiv:2312.14997: Section 2.1 (reproduction numbers and Definition of behaviours) and Theorems 1–2.
