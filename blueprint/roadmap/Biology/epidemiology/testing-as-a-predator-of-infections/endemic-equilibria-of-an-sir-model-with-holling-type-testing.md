# Endemic equilibria of an SIR model with Holling-type testing

**Model.** Susceptible $S$, untested infectious $I$, test-confirmed $C$, monitored $M$ and recovered $R$ (dimensionless):
$$\begin{aligned}
S' &= \alpha - cSI - \mu S, & I' &= cSI - \frac{pC}{\varepsilon + I + aM} I - \gamma I - \mu I,\\
C' &= \frac{pC}{\varepsilon + I + aM} I - (m + d + \mu) C, & M' &= mC - (q + \mu) M, \qquad R' = qM + \gamma I - \mu R,
\end{aligned}$$
where the daily test-positive rate $pCI/(\varepsilon + I + aM)$ is of Holling type II (testing acts like a predator that needs handling time), $m$ is the monitoring rate, $d$ the disease death rate of confirmed cases and $q$ the monitored recovery rate. The basic reproduction number is $\mathcal R_0 = c\alpha/(\mu(\mu + \gamma))$.

**Theorem.**
1. There is always a unique disease-free equilibrium $E_0$, globally asymptotically stable for $\mathcal R_0 \le 1$ and unstable for $\mathcal R_0 > 1$.
2. For $\mathcal R_0 > 1$ there is a unique testing-free endemic equilibrium $E_1$ ($C = M = 0$). If $p \le m + d + \mu$ there is no interior (testing) equilibrium, and for $p < m + d + \mu$ the equilibrium $E_1$ is globally asymptotically stable off the $S$-axis.
3. If $p > m + d + \mu$, let $b = \frac{a(m + d + \mu)}{p - m - d - \mu}$. When $\mathcal R_0 > 1 + \frac{\varepsilon b c}{a\mu}$ there is a unique interior endemic equilibrium $E_*$ with testing, and $I_* < I_1$.
4. With a Holling type I testing rate $pCI$, $E_1$ is globally asymptotically stable for $1 < \mathcal R_0 \le 1 + \frac{c(m + d + \mu)}{\mu p}$ and unstable above, where the unique interior equilibrium $E_*$ (existing for $\mathcal R_0 > 1 + \frac{c(m+d+\mu)}{\mu p}$) is globally asymptotically stable in the interior.

## Expansion

The testing compartment grows only by finding infected individuals, so testing persists only if the per-capita yield $p$ (at low infection prevalence) exceeds its loss rate $m + d + \mu$, exactly the predator invasion condition of predator–prey theory. When both endemic states exist, the testing state has lower prevalence, but the authors argue that random fluctuations driving testing low can trap the system near the testing-free endemic state ("stochastic trapping"), suggesting a testing-less endemic end of a pandemic. Global stability uses Lyapunov functions of Volterra type.

## Sources

- B. Deng, C. Yang, "Theory of Infectious Diseases with Testing and Testing-less Covid-19 Endemic", arXiv:2311.08611 (2023), Theorems 1.1, 1.2, 2.1 and 2.2, <https://doi.org/10.48550/arXiv.2311.08611>.
