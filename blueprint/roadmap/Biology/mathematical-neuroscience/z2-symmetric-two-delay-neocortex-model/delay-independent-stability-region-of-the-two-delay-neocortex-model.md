# Delay-independent stability region of the two-delay neocortex model

In the two-delay neocortex model with linearization coefficients $k_1, k_2$ and characteristic factors $\Delta_\pm(\lambda) = \lambda + 1 + k_1 e^{-\lambda\tau_1} \pm k_2 e^{-\lambda\tau_2}$ (see the dependency), assume $\tau_2 > \tau_1 > 0$.

**Theorem (eigenvalue bound).** If $\lambda = \rho + i\omega$ is a root of $\Delta_+\Delta_-$, then

$$|k_1| + |k_2| \ge e^{\rho\tau}\sqrt{(1 + \rho)^2 + \omega^2}, \qquad \tau = \begin{cases}\tau_2, & \rho < 0,\\ \tau_1, & \rho \ge 0.\end{cases}$$

**Corollary (stability square).** If $|k_1| + |k_2| < 1$, the equilibrium is asymptotically stable, for every pair of delays.

**Theorem (high frequencies cannot destabilize).** For $\omega_0 > 0$, the region $|k_1| + |k_2| < \sqrt{1 + \omega_0^2}$ contains no parameter values with a root $\pm i\omega$, $\omega \ge \omega_0$.

Consequently the region of stability around the origin of the $(k_1, k_2)$ plane extends from the square $|k_1| + |k_2| < 1$ to the nearest low-frequency bifurcation curve (the fold line $1 + k_1 - k_2 = 0$ and the branches of the Hopf curves $h_\pm(\omega)$ with $\omega < \omega_0$).

## Depends on

- [Symmetric equilibria and characteristic factorization of the two-delay neocortex model](symmetric-equilibria-and-characteristic-factorization.md)

## Expansion

From $\Delta_\pm(\lambda) = 0$, $|1 + \rho + i\omega| = |k_1 e^{-\lambda\tau_1} \pm k_2 e^{-\lambda\tau_2}| \le |k_1| e^{-\rho\tau_1} + |k_2| e^{-\rho\tau_2} \le e^{\max(-\rho\tau_1, -\rho\tau_2)}(|k_1| + |k_2|)$, and the maximum is attained at $\tau_2$ for $\rho < 0$ and at $\tau_1$ for $\rho \ge 0$. If $|k_1| + |k_2| < 1$ and $\rho \ge 0$, the bound would give $1 > e^{\rho\tau_1}\sqrt{(1+\rho)^2 + \omega^2} \ge 1$, which is impossible, so every root has $\rho < 0$. Setting $\rho = 0$ gives the high-frequency statement because $\sqrt{1 + \omega^2}$ increases in $\omega$. Since $k_1$ and $k_2$ are the gains of self-inhibition and mutual excitation, the square is a delay-independent sufficient condition for a stable background state, which the source relates to the action of anti-epileptic drugs on connection strengths.

## Sources

- S. Visser, H. G. E. Meijer, M. J. A. M. van Putten, S. A. van Gils, Analysis of stability and bifurcations of fixed points and periodic solutions of a lumped model of neocortex with two delays, Journal of Mathematical Neuroscience 2 (2012), Section 2.1 and 2.2 (Theorem 3, Corollary 4, Theorem 8). <https://doi.org/10.1186/2190-8567-2-8> PMCID: PMC3478171
