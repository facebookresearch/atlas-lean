# Time to first spike of a theta-modulated theta neuron

An excitatory gamma cell with phase $\theta_E \in [-\pi, \pi)$ receives slow periodic input of phase $\Theta$:

$$\frac{d\theta_E}{dt} = (1 - \cos\theta_E) + \bigl(I_E + \lambda(1 + \cos\Theta)\bigr)(1 + \cos\theta_E), \qquad \frac{d\Theta}{dt} = \varepsilon_\Theta\,\omega,$$

with drive $I_E$, coupling strength $\lambda > 0$ and $0 < \varepsilon_\Theta \ll 1$. A spike is the crossing $\theta_E = \pi$; inhibition is inactive before the first spike of a cycle, which starts at $\Theta = -\pi$, $t = 0$.

**Oscillatory regime ($I_E > 0$): exact solution.** With $V_E = \tan(\theta_E/2)$ the model is the quadratic integrate-and-fire neuron $\dot V_E = V_E^2 + I_E + \lambda(1 + \cos(\varepsilon_\Theta\omega t - \pi))$ with reset from $+\infty$ to $-\infty$. The substitution $V_E = -u'/u$ linearizes it to $u'' = -(I_E + \lambda(1 + \cos(\varepsilon_\Theta\omega t - \pi)))\,u$, and with

$$z = \frac{\varepsilon_\Theta\omega t}{2}, \qquad a = \frac{4(I_E + \lambda)}{\varepsilon_\Theta^2\omega^2}, \qquad q = \frac{2\lambda}{\varepsilon_\Theta^2\omega^2},$$

this is the Mathieu equation $\dfrac{d^2u}{dz^2} = -(a - 2q\cos 2z)\,u$. Spike times are the zeros of the solution $u$ (a combination of the Mathieu functions $\mathrm{Ce}(a,q,z)$ and $\mathrm{Se}(a,q,z)$ fixed by $V_E(0) = -\infty$), so the first spike time $T_1$ is the first zero of $u$, rescaled back to $t$.

**Excitable regime ($I_E < 0 < 2\lambda + I_E$): slow passage.** Spiking is possible only while $I_E + \lambda(1 + \cos\Theta) > 0$. Let $\Theta_0 \in (-\pi, 0)$ solve $\cos\Theta_0 = -(\lambda + I_E)/\lambda$, where the cell crosses the SNIC bifurcation, and let $a = 2\sqrt{-I_E(2\lambda + I_E)}$. Near $(\theta_E, \Theta) = (0, \Theta_0)$ the system reduces to $\dot x = y + x^2$, $\dot y = \tilde\varepsilon$ with $\tilde\varepsilon = a\varepsilon_\Theta\omega/2$.

**Proposition.** For the reduced system, a trajectory starting on the attracting branch of the nullcline $y = -x^2$ meets the line $x = \delta$ at height $h(\tilde\varepsilon) = -\Omega_0\,\tilde\varepsilon^{2/3} + O(\tilde\varepsilon\ln\tilde\varepsilon)$, where $\Omega_0 \approx -2.34$ is the smallest zero in absolute value of $J_{-1/3}(\tfrac23|y|^{3/2}) + J_{1/3}(\tfrac23|y|^{3/2})$, read on the negative axis. Consequently

$$T_1 = \frac{\Theta_0 + \pi}{\varepsilon_\Theta\,\omega} + C_0\,\varepsilon_\Theta^{-1/3} + O(\ln\varepsilon_\Theta), \qquad C_0 = -\frac{2^{1/3}\,\Omega_0}{(\omega a)^{1/3}} > 0.$$

## Expansion

The first term of $T_1$ is the time for the slow phase to reach the bifurcation value $\Theta_0$; the second is the delay of the jump past the fold, the classical $\varepsilon^{2/3}$ law for slow passage through a fold, which converts to an $\varepsilon_\Theta^{-1/3}$ time because $y$ moves at speed $\tilde\varepsilon$. The local reduction is the Riccati equation $dx/dy = (y + x^2)/\varepsilon$, solved by ratios of Bessel functions $J_{\pm1/3}, J_{\pm2/3}$; the trajectory blows up where the denominator first vanishes, which gives $\Omega_0$. Geometric singular perturbation theory and blow-up of the non-hyperbolic point make the estimate rigorous. In both regimes the first gamma spike is controlled mainly by the coupling $\lambda$ and the theta frequency. Spike times later in the cycle also depend on recurrent inhibition, and the same reduction counts gamma spikes per theta cycle.

## Sources

- L. Fontolan, M. Krupa, A. Hyafil, B. Gutkin, "Analytical insights on theta-gamma coupled neural oscillators", Journal of Mathematical Neuroscience (2013), Eqs. (1)–(18) and Proposition 1, <https://doi.org/10.1186/2190-8567-3-16>, PMCID PMC3848946.
