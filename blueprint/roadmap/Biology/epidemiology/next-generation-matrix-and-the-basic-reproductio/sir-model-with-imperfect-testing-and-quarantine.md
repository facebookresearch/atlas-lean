# SIR model with imperfect testing and quarantine

A population of constant size $N$ is split into susceptible $S$, infectious $I$ and recovered $R$ individuals, each with a quarantined counterpart $Q_S, Q_I, Q_R$. Individuals are tested for active infection at per-capita rate $\rho$ with sensitivity $\sigma_A$ and specificity $\tau_A$ (so false positives move $S$ and $R$ into quarantine at rate $\rho(1-\tau_A)$), quarantined individuals are tested for antibodies at rate $\phi$ with sensitivity $\sigma_B$ and specificity $\tau_B$ (releasing $Q_R$ at rate $\phi\sigma_B$ and, by false positives, $Q_S$ at rate $\phi(1-\tau_B)$), immunity wanes at rate $\alpha$, recovery occurs at rate $\gamma$ and transmission at rate $\beta$ among non-quarantined individuals. All rates are nonnegative with $N > 0$ and $\gamma > 0$, and sensitivities and specificities lie in $[0, 1]$. The system is considered where the mixing population is nonempty, $N - Q_S - Q_I - Q_R > 0$:

$$\begin{aligned}
S' &= -\frac{\beta S I}{N - Q_S - Q_I - Q_R} + \alpha R + \phi(1-\tau_B)Q_S - \rho(1-\tau_A)S,\\
Q_S' &= \rho(1-\tau_A)S - \phi(1-\tau_B)Q_S,\\
I' &= \frac{\beta S I}{N - Q_S - Q_I - Q_R} - \rho\sigma_A I - \gamma I,\\
Q_I' &= \rho\sigma_A I - \gamma Q_I,\\
R' &= \gamma(I + Q_I) - \rho(1-\tau_A)R + \phi\sigma_B Q_R - \alpha R,\\
Q_R' &= \rho(1-\tau_A)R - \phi\sigma_B Q_R.
\end{aligned}$$

The total $S + Q_S + I + Q_I + R + Q_R$ is conserved; when it equals $N$, the mixing population is $N - Q_S - Q_I - Q_R = S + I + R$.

**Reproduction number.** Consider a disease-free state with $I = Q_I = R = Q_R = 0$, $S > 0$ and $S + Q_S = N$. It is an equilibrium exactly when the testing flows of susceptibles balance,

$$\rho(1-\tau_A)S = \phi(1-\tau_B)Q_S;$$

in particular $(S, Q_S) = (N, 0)$ is an equilibrium only when $\rho(1-\tau_A) = 0$, since false positives otherwise move susceptibles into quarantine. With infected compartments $(I, Q_I)$, the next-generation matrices at such an equilibrium are

$$F = \begin{pmatrix}\beta & 0\\ 0 & 0\end{pmatrix}, \qquad V = \begin{pmatrix}\gamma + \rho\sigma_A & 0\\ -\rho\sigma_A & \gamma\end{pmatrix}, \qquad FV^{-1} = \begin{pmatrix}\dfrac{\beta}{\gamma + \rho\sigma_A} & 0\\ 0 & 0\end{pmatrix},$$

where $V$ is invertible because it is lower triangular with positive diagonal entries $\gamma + \rho\sigma_A$ and $\gamma$, so

$$\mathcal R_0 = \frac{\beta}{\gamma + \rho\sigma_A}.$$

Test sensitivity and testing rate lower $\mathcal R_0$ by shortening the infectious period outside quarantine; specificity and the antibody test do not enter $\mathcal R_0$, but they determine how many susceptible and recovered individuals sit in quarantine.

## Depends on

- [Basic reproduction number of the next-generation matrix](r0.md)

## Proof depends on

- [Eigenvalues of a block lower-triangular matrix](mem-spectrum-from-blocks-zero.md)

## Expansion

New infections appear only in $I$ at rate $\beta S I/(N - Q_S - Q_I - Q_R)$; linearizing at the disease-free equilibrium above, where $I = Q_I = R = Q_R = 0$ and $N - Q_S = S > 0$, gives $\partial_I = \beta S/(N - Q_S) = \beta$ and $\partial_{Q_I} = 0$, so $\beta$ is the only non-zero entry of $F$. The paper evaluates it at $S = N$, $Q_S = 0$, with the same value, although that point is an equilibrium only without false positives; the value $\beta$ does not depend on how the susceptibles are split between $S$ and $Q_S$. Transitions out of $I$ occur at rate $\gamma + \rho\sigma_A$, and $Q_I$ is fed from $I$ at rate $\rho\sigma_A$ and left at rate $\gamma$, which gives $V$. Since $FV^{-1}$ is block triangular with diagonal blocks $\beta(V^{-1})_{11}$ and $0$, its eigenvalues are $\beta/(\gamma + \rho\sigma_A)$ and $0$, and its spectral radius is $\beta\,(V^{-1})_{11} = \beta/(\gamma + \rho\sigma_A)$. This is a modified and extended form of a testing model of Gray et al. (2020) used to study relaxation of distancing under imperfect tests.

## Sources

- O. Akman, S. Chauhan, A. Ghosh et al., "The hard lessons and shifting modeling trends of COVID-19 dynamics: multiresolution modeling approach", Bulletin of Mathematical Biology (2021), section "Diagnostic Test Model" (system 1 and its next-generation computation), <https://doi.org/10.1007/s11538-021-00959-4> (PMC8602007).
