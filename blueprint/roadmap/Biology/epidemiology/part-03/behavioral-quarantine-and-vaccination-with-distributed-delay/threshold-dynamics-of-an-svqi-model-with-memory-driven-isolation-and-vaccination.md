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

**Proposition.** If $R_0 > 1$ and either $q_1, q_2$ are small, or $\delta$ is large and $q_2$ small, the unique endemic equilibrium is locally asymptotically stable.

*Purely imaginary roots for the uniform kernel.* Let $R_0 > 1$ and take the uniform kernel $f = L^{-1}\mathbf 1_{(T,T+L)}$ (so $\tau \ge T + L$), with reporting delay $T \ge 0$ as the bifurcation parameter and fixed window $L > 0$. Linearizing at an endemic equilibrium $\overline E = (\overline S, \overline V, \overline Q, \overline I)$ gives the characteristic equation

$$\zeta^4 + A_3\zeta^3 + A_2\zeta^2 + A_1\zeta + A_0 + \bigl(B_2\zeta^2 + B_1\zeta + B_0\bigr)\,\frac{1 - e^{-\zeta L}}{\zeta L}\,e^{-\zeta T} = 0,$$

where $A_0, \dots, A_3$ and $B_0, B_1, B_2$ are explicit real coefficients determined by the parameters and by $\overline E$, independent of $T$ and $L$. For $x \ge 0$ let

$$K(x) = x^5 + c_4x^4 + c_3x^3 + c_2x^2 + c_1x + \bigl(r_2x^2 + r_1x + r_0\bigr)\bigl(1 - \cos(\sqrt{x}\,L)\bigr),$$

with $c_4 = A_3^2 - 2A_2$, $c_3 = A_2^2 + 2A_0 - 2A_1A_3$, $c_2 = A_1^2 - 2A_0A_2$, $c_1 = A_0^2$, $r_2 = -2B_2^2/L^2$, $r_1 = -2(B_1^2 - 2B_0B_2)/L^2$ and $r_0 = -2B_0^2/L^2$ ($K$ is not a polynomial). Then, for $w > 0$, $K(w^2) = 0$ if and only if there is $T^* > 0$ such that the characteristic equation has a unique conjugate pair of purely imaginary roots $\pm iw$ exactly when $T \in \{T^* + 2n\pi/w : n \in \mathbb N\}$. If $\pm i\sqrt{x^*}$ are such roots and $K'(x^*) > 0$ (respectively $K'(x^*) < 0$), then as $T$ increases the pair crosses the imaginary axis from left to right (respectively from right to left).

These crossings are where the endemic equilibrium can lose or regain stability through Hopf bifurcations as the reporting delay grows, producing recurrent epidemic waves.

Since behavioural responses act only through the history of $I$ and vanish at $I = 0$, they do not change $R_0$: memory-driven isolation and vaccination shape the endemic state and its oscillations, not the invasion threshold.

## Expansion

At the disease-free state $f * I = 0$, so $g_1 = g_2 = 0$, $V = Q = 0$ and $S = b/\mu$; the next-generation matrix is scalar, $F V^{-1} = (b\beta/\mu)/(\gamma + \mu)$. Global stability for $R_0 \le 1$ uses a Lyapunov–LaSalle functional on $\Gamma$ exploiting $S + \sigma Q \le b/\mu$. Endemic equilibria satisfy $\beta \overline S + \sigma\beta \overline Q = \gamma + \mu$, and eliminating $\overline S, \overline V, \overline Q$ yields a cubic-type equation in $\overline I$ because $h$ is rational in $\overline I$, which explains up to three equilibria. For the uniform kernel, $\int f(a)e^{-\zeta a}\,da = \frac{1 - e^{-\zeta L}}{\zeta L}e^{-\zeta T}$. Substituting $\zeta = iw$ writes the characteristic equation as $P_1(w) = P_2(w)e^{-iwT}$; equating moduli, $|P_1(w)| = |P_2(w)|$, and using $|1 - e^{iwL}|^2 = 2(1 - \cos wL)$ gives $K(w^2) = 0$, and the phase condition $e^{-iwT} = P_1(w)/P_2(w)$ then fixes the critical delays $T^*(w) + 2n\pi/w$.

## Sources

- Mehdi Bouziane, Silia Bercisse, Abdennasser Chekroun, Simon Girel, "How delay, isolation and vaccination shape epidemic waves: a bifurcation approach in mathematical epidemiology", arXiv (2026). Model assumptions (A1)–(A4) and system (sysmprinciple), next-generation computation of $R_0$, Theorems 1–4, Propositions 5, 7 and 8, Theorem 6. <https://doi.org/10.48550/arXiv.2603.24107>. Published version: Journal of Applied Mathematics and Computing 72(3) (2026), article 112, <https://doi.org/10.1007/s12190-026-02765-4>; locators above refer to the arXiv version.
