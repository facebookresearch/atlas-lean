# Exponential relaxation under the sliding-memory Caputo derivative

Let $\alpha \in (0,1)$, $L > 0$ and $k > 0$, and let ${}^{\mathrm{MC}}_{L}D_t^{\alpha}$ be the Caputo derivative with sliding memory window $[t-L,t]$. The relaxation equation

$$ {}^{\mathrm{MC}}_{L}D_t^{\alpha} z(t) = -k\, z(t) $$

has exponential solutions $z(t) = z(0) e^{-\lambda t}$, and the admissible rate is the unique $\lambda > 0$ solving

$$ \lambda \int_0^L u^{-\alpha} e^{\lambda u}\, du = k\, \Gamma(1-\alpha) . $$

**Local stability of the fractional chemostat equilibrium.** For the reduced periodic Contois chemostat ${}^{\mathrm{MC}}_{L}D_t^{\alpha} s = \vartheta^{1-\alpha}\big[\bar D - \nu(s)\big](s_{\mathrm{in}} - s)$ with constant dilution $\bar D < \mu_{\max}$, linearizing at the equilibrium $\bar s$ (where $\nu(\bar s) = \bar D$) gives the relaxation equation with

$$ k = \vartheta^{1-\alpha}\, \nu'(\bar s)\, (s_{\mathrm{in}} - \bar s) > 0 , $$

so perturbations decay like $e^{-\lambda t}$; solutions started below (above) $\bar s$ approach it monotonically from below (above) without reaching it in finite time, so a constant dilution rate admits no nonconstant $T$-periodic solution near $\bar s$.

## Depends on

- [Periodic chemostat with a sliding-memory Caputo derivative](periodic-sliding-memory-fractional-chemostat.md)

## Expansion

Substituting $z(0)e^{-\lambda t}$ and setting $u = t - \tau$ gives ${}^{\mathrm{MC}}_{L}D_t^{\alpha} z = -\lambda z(t)\,\Gamma(1-\alpha)^{-1}\int_0^L u^{-\alpha} e^{\lambda u}\,du$. The function $\psi(\lambda) = \lambda\int_0^L u^{-\alpha}e^{\lambda u}\,du$ is continuous, strictly increasing on $(0,\infty)$, tends to $0$ as $\lambda \to 0^+$ and to $\infty$ as $\lambda\to\infty$, so the intermediate value theorem yields exactly one positive root. Unlike the classical Caputo case, where relaxation is of Mittag-Leffler (power-law) type, the finite memory window restores a purely exponential mode. The sign of $\nu'$ is positive because $\nu$ is increasing on $(0, s_{\mathrm{in}})$.

## Sources

- Kareem T. Elgindy, Muneerah Al Nuwairan, Liew Siaw Ching, "Periodic fractional control in bioprocesses for clean water and ecosystem health", AIMS Mathematics 11 (2026), 1712–1760, <https://doi.org/10.3934/math.2026072>. Published version of arXiv:2508.01022, cited next; locators there refer to the arXiv version.
- K. T. Elgindy, M. Al Nuwairan, L. S. Ching, "Periodic Fractional Control in Bioprocesses for Clean Water and Ecosystem Health", arXiv:2508.01022 (2025), Appendix C, Lemma 3 and Theorem 4 (local stability of the equilibrium). <https://doi.org/10.48550/arXiv.2508.01022>
