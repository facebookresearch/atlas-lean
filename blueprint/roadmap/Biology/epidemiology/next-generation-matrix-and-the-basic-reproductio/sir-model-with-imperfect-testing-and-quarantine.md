# SIR model with imperfect testing and quarantine

A population of constant size $N$ is split into susceptible $S$, infectious $I$ and recovered $R$ individuals, each with a quarantined counterpart $Q_S, Q_I, Q_R$. Individuals are tested for active infection at per-capita rate $\rho$ with sensitivity $\sigma_A$ and specificity $\tau_A$ (so false positives move $S$ and $R$ into quarantine at rate $\rho(1-\tau_A)$), quarantined individuals are tested for antibodies at rate $\phi$ with sensitivity $\sigma_B$ and specificity $\tau_B$ (releasing $Q_R$ at rate $\phi\sigma_B$ and, by false positives, $Q_S$ at rate $\phi(1-\tau_B)$), immunity wanes at rate $\alpha$, recovery occurs at rate $\gamma$ and transmission at rate $\beta$ among non-quarantined individuals:

$$\begin{aligned}
S' &= -\frac{\beta S I}{N - Q_S - Q_I - Q_R} + \alpha R + \phi(1-\tau_B)Q_S - \rho(1-\tau_A)S,\\
Q_S' &= \rho(1-\tau_A)S - \phi(1-\tau_B)Q_S,\\
I' &= \frac{\beta S I}{N - Q_S - Q_I - Q_R} - \rho\sigma_A I - \gamma I,\\
Q_I' &= \rho\sigma_A I - \gamma Q_I,\\
R' &= \gamma(I + Q_I) - \rho(1-\tau_A)R + \phi\sigma_B Q_R - \alpha R,\\
Q_R' &= \rho(1-\tau_A)R - \phi\sigma_B Q_R.
\end{aligned}$$

**Reproduction number.** With infected compartments $(I, Q_I)$, the next-generation matrices at a disease-free equilibrium are

$$F = \begin{pmatrix}\beta & 0\\ 0 & 0\end{pmatrix}, \qquad V = \begin{pmatrix}\gamma + \rho\sigma_A & 0\\ -\rho\sigma_A & \gamma\end{pmatrix}, \qquad FV^{-1} = \begin{pmatrix}\dfrac{\beta}{\gamma + \rho\sigma_A} & 0\\ 0 & 0\end{pmatrix},$$

so

$$\mathcal R_0 = \frac{\beta}{\gamma + \rho\sigma_A}.$$

Test sensitivity and testing rate lower $\mathcal R_0$ by shortening the infectious period outside quarantine; specificity and the antibody test do not enter $\mathcal R_0$, but they determine how many susceptible and recovered individuals sit in quarantine.

## Depends on

- [Basic reproduction number of the next-generation matrix](r0.md)
- [Kermack–McKendrick SIR model](../kermack-mckendrick-sir-model/README.md)

## Expansion

New infections appear only in $I$ at rate $\beta S I/(N - Q_S - Q_I - Q_R)$; linearizing at a disease-free state, where $I = Q_I = R = Q_R = 0$ and $S + Q_S = N$, gives $\partial_I = \beta S/(N - Q_S) = \beta$, which is the only non-zero entry of $F$ (the paper evaluates it at $S = N$, $Q_S = 0$, with the same result). Transitions out of $I$ occur at rate $\gamma + \rho\sigma_A$, and $Q_I$ is fed from $I$ at rate $\rho\sigma_A$ and left at rate $\gamma$, which gives $V$. Since $F$ has rank one, the spectral radius of $FV^{-1}$ is its $(1,1)$ entry $\beta\,(V^{-1})_{11} = \beta/(\gamma + \rho\sigma_A)$. This is a modified and extended form of a testing model of Gray et al. (2020) used to study relaxation of distancing under imperfect tests.

## Sources

- O. Akman, S. Chauhan, A. Ghosh et al., "The hard lessons and shifting modeling trends of COVID-19 dynamics: multiresolution modeling approach", Bulletin of Mathematical Biology (2021), section "Diagnostic Test Model" (system 1 and its next-generation computation), <https://doi.org/10.1007/s11538-021-00959-4> (PMC8602007).
