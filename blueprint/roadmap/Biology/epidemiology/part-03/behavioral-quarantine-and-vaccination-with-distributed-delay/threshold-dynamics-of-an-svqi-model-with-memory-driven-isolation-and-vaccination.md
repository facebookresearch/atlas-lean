# Threshold dynamics of an SVQI model with memory-driven isolation and vaccination

Susceptibles $S$, vaccinated $V$, voluntarily isolated (quarantined) $Q$ and infectives $I$ react to the recent history of infection through the weighted memory

$$(f * I)(t) = \int_0^\tau f(s)\,I(t-s)\,ds, \qquad f \ge 0, \quad \int_0^\tau f = 1,$$

which drives isolation at rate $g_1(f*I) = q_1 (f*I)$, vaccination at rate $g_2(f*I) = q_2(f*I)$, and return from isolation at the decreasing rate $h(f*I) = \delta/(1 + \alpha (f*I))$:

$$S' = b - \beta SI - g_1(f*I)S - g_2(f*I)S - \mu S + h(f*I)Q + \rho V,$$

$$V' = g_2(f*I)S + \lambda Q - (\rho + \mu)V, \qquad Q' = g_1(f*I)S - h(f*I)Q - \sigma\beta QI - (\lambda + \mu)Q,$$

$$I' = \beta SI + \sigma\beta QI - (\gamma + \mu)I,$$

with recruitment $b$, transmission $\beta$, natural death $\mu$, recovery $\gamma$, waning of vaccine protection $\rho$, transfer from isolation to vaccination $\lambda$, and imperfect isolation $0 \le \sigma < 1$; all constants positive. The basic reproduction number is

$$R_0 = \frac{b\beta}{\mu(\gamma + \mu)}.$$

**Theorem.** For nonnegative continuous initial histories on $[-\tau,0]$ the system has a unique nonnegative bounded solution, and the region $\Gamma = \{S + V + Q + I \le b/\mu\}$ is positively invariant. The disease-free equilibrium $E^0 = (b/\mu, 0, 0, 0)$ always exists; it is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$, and globally asymptotically stable in $\Gamma$ if $R_0 \le 1$. Endemic equilibria exist if and only if $R_0 > 1$, and there can be one, two or three of them.

**Proposition.** If $R_0 > 1$ and either $q_1, q_2$ are small, or $\delta$ is large and $q_2$ small, the unique endemic equilibrium is locally asymptotically stable. For a memory kernel concentrated at a delay $T$, purely imaginary characteristic roots $\pm i\omega$ occur exactly at $T \in \{T^* + 2n\pi/\omega : n \in \mathbb N\}$ for each positive root $\omega^2$ of an explicit polynomial $K$, and the roots cross the imaginary axis transversally in the direction of $\operatorname{sign} K'(\omega^2)$, so Hopf bifurcations produce recurrent epidemic waves as the behavioural delay grows.

Since behavioural responses act only through the history of $I$ and vanish at $I = 0$, they do not change $R_0$: memory-driven isolation and vaccination shape the endemic state and its oscillations, not the invasion threshold.

## Expansion

At the disease-free state $f * I = 0$, so $g_1 = g_2 = 0$, $V = Q = 0$ and $S = b/\mu$; the next-generation matrix is scalar, $F V^{-1} = (b\beta/\mu)/(\gamma + \mu)$. Global stability for $R_0 \le 1$ uses a Lyapunov–LaSalle functional on $\Gamma$ exploiting $S + \sigma Q \le b/\mu$. Endemic equilibria satisfy $\beta \overline S + \sigma\beta \overline Q = \gamma + \mu$, and eliminating $\overline S, \overline V, \overline Q$ yields a cubic-type equation in $\overline I$ because $h$ is rational in $\overline I$, which explains up to three equilibria. Linearizing around an endemic equilibrium gives a transcendental characteristic equation; substituting $\zeta = i\omega$ and separating real and imaginary parts produces the polynomial condition $K(\omega^2) = 0$ and the critical delays.

## Sources

- Mehdi Bouziane, Silia Bercisse, Abdennasser Chekroun, Simon Girel, "How delay, isolation and vaccination shape epidemic waves: a bifurcation approach in mathematical epidemiology", arXiv (2026). Model assumptions (A1)–(A4) and system (sysmprinciple), next-generation computation of $R_0$, Theorems 1–4, Propositions 5, 7 and 8, Theorem 6. <https://doi.org/10.48550/arXiv.2603.24107>. Published version: Journal of Applied Mathematics and Computing 72(3) (2026), article 112, <https://doi.org/10.1007/s12190-026-02765-4>; locators above refer to the arXiv version.
