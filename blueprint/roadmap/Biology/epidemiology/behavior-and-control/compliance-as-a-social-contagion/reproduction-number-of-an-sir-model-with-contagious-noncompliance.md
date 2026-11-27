# Reproduction number of an SIR model with contagious noncompliance

**Model.** Compliant classes $S, I, R$ and noncompliant classes $S^*, I^*, R^*$, with $N^* = S^* + I^* + R^*$ and actively mixing infectives $I^{(M)} = (1 - \alpha) I + I^*$, where $\alpha \in [0,1]$ is the efficacy of the protocol:

$$\begin{aligned}
\dot S &= (1-\xi) b - \beta(1-\alpha) S I^{(M)} - \mu S N^* + \nu S^* - \delta S, & \dot S^* &= \xi b - \beta S^* I^{(M)} + \mu S N^* - \nu S^* - \delta S^*,\\
\dot I &= \beta(1-\alpha) S I^{(M)} - \gamma I - \mu I N^* + \nu I^* - \delta I, & \dot I^* &= \beta S^* I^{(M)} - \gamma I^* + \mu I N^* - \nu I^* - \delta I^*,\\
\dot R &= \gamma I - \mu R N^* + \nu R^* - \delta R, & \dot R^* &= \gamma I^* + \mu R N^* - \nu R^* - \delta R^*.
\end{aligned}$$

Noncompliance spreads by contact at rate $\mu$ and is abandoned at rate $\nu$; recruits ($b$) are noncompliant with probability $\xi$; $\delta$ is the death rate.

**Theorem.** At a disease-free state with susceptible densities $(s, s^*)$, the next-generation matrix has rank one and

$$\mathscr R_0(s, s^*) = \frac{\beta}{\gamma + \delta}\left( s\Bigl[(1-\alpha)^2 + \frac{\alpha(1-\alpha)\mu s^*}{\gamma + \delta + \nu + \mu s^*}\Bigr] + s^*\Bigl[1 - \frac{\alpha \nu}{\gamma + \delta + \nu + \mu s^*}\Bigr]\right).$$

For $\xi = 0$ the disease-free equilibria are $x_1 = (b/\delta, 0, 0, 0, 0, 0)$ and, when $b/\delta > (\delta + \nu)/\mu$, $x_2$ with $s = (\delta + \nu)/\mu$, $s^* = b/\delta - (\delta+\nu)/\mu$ (a noncompliance-endemic, disease-free state). If $b/\delta < (\delta + \nu)/\mu$, $x_1$ is locally asymptotically stable when $\mathscr R_0(b/\delta, 0) < 1$ and unstable when $> 1$; if $b/\delta > (\delta+\nu)/\mu$ the analogous statement holds for $x_2$ with $\mathscr R_0(s, s^*)$. **Stochastic model.** Perturb $\beta$ and $\mu$ by a scalar Brownian motion $W$ with intensities $\sigma_\beta, \sigma_\mu \ge 0$, with noise terms proportional to the class they act on: the drifts are those above, and the diffusion coefficients (multiplying $dW$) are

$$\begin{aligned}
dS&: -\sigma_\beta(1-\alpha)^2SI - \sigma_\mu SS^*, & dS^*&: -\sigma_\beta S^*I^* + \sigma_\mu SS^*,\\
dI&: \sigma_\beta(1-\alpha)^2SI - \sigma_\mu II^*, & dI^*&: \sigma_\beta S^*I^* + \sigma_\mu II^*,\\
dR&: -\sigma_\mu RR^*, & dR^*&: \sigma_\mu RR^*.
\end{aligned}$$

For positive initial data this system has a unique global nonnegative solution almost surely. For $\xi = 0$ define the noise-corrected threshold at $x_1$,

$$\mathscr R_0^\sigma\Bigl(\frac b\delta, 0\Bigr) = \frac{\beta\frac b\delta(1-\alpha)^2 + \frac{\sigma_\beta^2}{2}\bigl(\frac b\delta\bigr)^2(1-\alpha)^4}{\gamma + \delta}.$$

If $\mathscr R_0^\sigma(b/\delta, 0) < 1$ and $\frac{b}{\delta} + \frac{\sigma_\mu^2}{2\mu}\bigl(\frac{b}{\delta}\bigr)^2 < \frac{\nu + \delta}{\mu}$, the fully compliant disease-free state $x_1$ is exponentially mean-square stable for the stochastic system.

## Expansion

Only $I$ and $I^*$ generate new infections, so the infection subsystem is two-dimensional; new infections enter both groups in proportion to $I^{(M)}$, which makes the transmission matrix rank one, and $\mathscr R_0$ is its single nonzero eigenvalue after accounting for transfers between groups during the infectious period. The formula is a weighted average of the compliant reproduction ratio $(1-\alpha)^2 \beta s/(\gamma+\delta)$ and the noncompliant one $\beta s^*/(\gamma+\delta)$, corrected by the chance of switching group while infectious. The condition $b/\delta \gtrless (\delta + \nu)/\mu$ is the threshold for noncompliance itself to persist as a social contagion.

## Sources

- C. Parkinson, W. Wang, "A Compartmental Model for Epidemiology with Human Behavior and Stochastic Effects", *Mathematical Biosciences* 392 (2026), 109588, Proposition 2.4, Theorems 2.3 and 2.5, system (3.1), Theorem 3.1, threshold (4.2) and Theorem 4.2, <https://doi.org/10.1016/j.mbs.2025.109588> (preprint arXiv:2507.01046).
