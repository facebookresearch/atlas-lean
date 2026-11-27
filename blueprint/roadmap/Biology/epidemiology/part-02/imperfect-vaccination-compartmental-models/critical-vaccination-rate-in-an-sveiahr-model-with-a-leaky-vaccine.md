# Critical vaccination rate in an SVEIAHR model with a leaky vaccine

**Model.** Compartments $S, V, E, I, A, H, R$ (susceptible, vaccinated, exposed, symptomatic, asymptomatic, hospitalized, recovered), $N$ their sum:

$$\begin{aligned}
\dot S &= (1-p)\Pi + \eta R - (\beta_S + \mu + v) S, & \dot A &= \sigma(1-\psi) E - g_5 A,\\
\dot V &= p\Pi + v S - (\beta_V + \mu) V, & \dot H &= \gamma(1-\kappa) I - g_6 H,\\
\dot E &= \beta_S S + \beta_V V - g_3 E, & \dot R &= \gamma\kappa I + \lambda\phi A + \tau H - (\eta + \mu) R,\\
\dot I &= \sigma\psi E + \lambda(1-\phi) A - g_4 I, & &
\end{aligned}$$

with forces of infection $\beta_S = b(\omega_A A + \omega_I I + \omega_H H)/N$ and $\beta_V = (1-\varepsilon)\beta_S$, recruitment $\Pi$ with vaccinated fraction $p$, vaccination rate $v \ge 0$, vaccine efficacy $\varepsilon \in [0,1]$, and $g_1 = \mu + v$, $g_2 = \mu$, $g_3 = \sigma + \mu$, $g_4 = \gamma + \mu + \delta$, $g_5 = \lambda + \mu$, $g_6 = \tau + \mu + \delta$. The region $\{N \le \Pi/\mu\}$ of $\mathbb{R}^7_{\ge 0}$ is positively invariant.

**Reproduction number.** The disease-free equilibrium has $S^0 = (1-p)\Pi/g_1$, $V^0 = \Pi(p g_1 + v(1-p))/(g_1 g_2)$, and

$$\mathcal{R}_0(v) = \mathcal{R}_0 \cdot \frac{\mu(1-p) + (1-\varepsilon)(p\mu + v)}{\mu + v}, \qquad \mathcal{R}_0 = \frac{b\sigma\,(G_1 G_2 + G_3)}{g_3 g_4 g_5 g_6},$$

where $G_1 = \lambda(1-\phi)(1-\psi) + g_5\psi$, $G_2 = g_6\omega_I + \gamma(1-\kappa)\omega_H$, $G_3 = g_4 g_6 (1-\psi)\omega_A$; $\mathcal{R}_0$ is the reproduction number in a fully susceptible population.

**Results.**

1. If $\mathcal{R}_0(v) < 1$, the disease-free equilibrium is locally asymptotically stable; it need not be globally stable, since recovered hosts return to the fully susceptible class and endemic equilibria can coexist with it below threshold. If $\mathcal{R}_0(v) > 1$ there is a unique endemic equilibrium, the positive root of a quadratic in the force of infection whose constant term is proportional to $\mathcal{R}_0(v) - 1$.
2. $\mathcal{R}_0(v)$ is strictly decreasing in $v$ when $\varepsilon > 0$ and $p < 1$ (constant when $\varepsilon = 0$ or $p = 1$), with $\lim_{v \to \infty}\mathcal{R}_0(v) = (1-\varepsilon)\mathcal{R}_0$. Hence elimination by vaccination is possible only if $\varepsilon > \varepsilon^* = 1 - 1/\mathcal{R}_0$.
3. If $\mathcal{R}_0 > 1$, $\mathcal{R}_0(1 - \varepsilon p) > 1$ and $\varepsilon > \varepsilon^*$, the critical vaccination rate

    $$v^* = \frac{\mu\,[(1 - \varepsilon p)\mathcal{R}_0 - 1]}{(\varepsilon - \varepsilon^*)\,\mathcal{R}_0} > 0$$

    satisfies $\mathcal{R}_0(v^*) = 1$, and $\mathcal{R}_0(v) \gtrless 1$ according as $v \lessgtr v^*$.

## Expansion

An exposed individual becomes symptomatic directly with probability $\sigma\psi/g_3$ or via the asymptomatic class with probability $\sigma(1-\psi)\lambda(1-\phi)/(g_3 g_5)$, and contributes infectiousness $\omega_A/g_5$ while asymptomatic, $\omega_I/g_4$ while symptomatic and $\omega_H\gamma(1-\kappa)/(g_4 g_6)$ while hospitalized; summing gives $\sigma(G_1G_2 + G_3)/(g_3g_4g_5g_6)$ per exposed individual. The second factor in $\mathcal{R}_0(v)$ is the susceptibility-weighted fraction $(S^0 + (1-\varepsilon)V^0)/N^0$. Its derivative in $v$ has the sign of $-\varepsilon\mu(1-p)$, giving monotonicity, and solving $\mathcal{R}_0(v) = 1$, a linear equation in $v$, gives $v^*$, using $(\varepsilon - \varepsilon^*)\mathcal{R}_0 = 1 - (1-\varepsilon)\mathcal{R}_0$. A leaky vaccine cannot by itself eliminate a pathogen whose $\mathcal{R}_0$ exceeds $1/(1-\varepsilon)$, however fast it is delivered.

## Sources

- M. L. Diagne, H. Rwezaura, S. Y. Tchoumi, J. M. Tchuenche, "A Mathematical Model of COVID-19 with Vaccination and Treatment", Computational and Mathematical Methods in Medicine 2021 (2021) 1250129, Sections 2–3 (model (2), equations (7)–(10), Theorem 1, Lemmas 1–2, equation (22)), <https://doi.org/10.1155/2021/1250129>.
