# Periodic chemostat with a sliding-memory Caputo derivative

Fix a period $T > 0$, a memory length $L > 0$ and an order $\alpha \in (0,1)$. For an absolutely continuous function $f$ the left-sided Caputo derivative with sliding memory is

$$ {}^{\mathrm{MC}}_{L}D_t^{\alpha} f(t) = \frac{1}{\Gamma(1-\alpha)} \int_{t-L}^{t} (t-\tau)^{-\alpha} f'(\tau)\, d\tau , $$

which keeps the Caputo kernel but only remembers the window $[t-L, t]$.

**Zero mean over a period.** If $s$ is absolutely continuous and $T$-periodic, then for every $L > 0$ and $\alpha \in (0,1]$

$$ \int_0^T {}^{\mathrm{MC}}_{L}D_t^{\alpha} s(t)\, dt = 0 . $$

**Fractional Contois chemostat.** With substrate $s(t)$, biomass $x(t)$, inlet concentration $s_{\mathrm{in}} > 0$, yield $Y > 0$, time-scaling constant $\vartheta > 0$, $T$-periodic dilution rate $D(t)$ and Contois growth $\mu(s,x) = \mu_{\max} s / (K x + s)$ with $\mu_{\max}, K > 0$, consider the $T$-periodic solutions of

$$ {}^{\mathrm{MC}}_{L}D_t^{\alpha} s = \vartheta^{1-\alpha}\Big[-\tfrac{1}{Y}\mu(s,x)\,x + D(t)(s_{\mathrm{in}} - s)\Big], \qquad {}^{\mathrm{MC}}_{L}D_t^{\alpha} x = \vartheta^{1-\alpha}\big[\mu(s,x) - D(t)\big] x . $$

The combination $z = Y(s_{\mathrm{in}} - s) - x$ satisfies ${}^{\mathrm{MC}}_{L}D_t^{\alpha} z = -\vartheta^{1-\alpha} D(t) z$ and has no nontrivial periodic solution, so periodic solutions lie on $x = Y(s_{\mathrm{in}} - s)$ and the system reduces to the scalar equation

$$ {}^{\mathrm{MC}}_{L}D_t^{\alpha} s = \vartheta^{1-\alpha}\big(D(t) - \nu(s)\big), \qquad \nu(s) = \frac{\mu_{\max} s}{K Y (s_{\mathrm{in}} - s) + s} . $$

For a constant dilution rate $D \equiv \bar D < \mu_{\max}$ the nontrivial equilibrium is

$$ \bar s = \frac{\bar D K Y s_{\mathrm{in}}}{\bar D K Y + \mu_{\max} - \bar D}, $$

which satisfies $0 < \bar s < s_{\mathrm{in}}$ and $\nu(\bar s) = \bar D$, with positive biomass $Y(s_{\mathrm{in}} - \bar s)$.

## Depends on

- [Chemostat equilibria and the washout threshold](chemostat-equilibria-and-washout.md)

## Expansion

The zero-mean identity follows by Fubini: after the change of variables $u = t - \tau$ the integral becomes $\Gamma(1-\alpha)^{-1}\int_0^L u^{-\alpha} \int_0^T s'(t-u)\, dt\, du$, and the inner integral vanishes because $s'$ is $T$-periodic with zero mean. This is what makes the sliding window compatible with periodic boundary conditions, unlike a Caputo derivative with fixed lower limit. The equilibrium is obtained by solving $\nu(s) = \bar D$, i.e. $\mu_{\max} s = \bar D K Y (s_{\mathrm{in}} - s) + \bar D s$; the condition $\bar D < \mu_{\max}$ excludes washout.

## Sources

- Kareem T. Elgindy, Muneerah Al Nuwairan, Liew Siaw Ching, "Periodic fractional control in bioprocesses for clean water and ecosystem health", AIMS Mathematics 11 (2026), 1712–1760, <https://doi.org/10.3934/math.2026072>. Published version of arXiv:2508.01022, cited next; locators there refer to the arXiv version.
- K. T. Elgindy, M. Al Nuwairan, L. S. Ching, "Periodic Fractional Control in Bioprocesses for Clean Water and Ecosystem Health", arXiv:2508.01022 (2025), Section 2.2 (sliding-memory Caputo derivative), Section 3 (problem statement and Contois model), Section 4 (reduction, Eqs. for the reduced equation and equilibrium) and Appendix A, Lemma 1. <https://doi.org/10.48550/arXiv.2508.01022>
