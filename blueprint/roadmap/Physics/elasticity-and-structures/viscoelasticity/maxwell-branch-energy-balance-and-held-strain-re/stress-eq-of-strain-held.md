# Stress relaxation of a Maxwell branch

Let a Maxwell branch have modulus $E > 0$ and viscosity $\eta > 0$, and let stress and strain histories $\sigma$ and $\varepsilon$ obey [the constitutive relation](is-history.md) on $[0, \infty)$. That is, at every $t \ge 0$, including $t = 0$, both histories are differentiable at $t$ in the ordinary two-sided sense (so at $t = 0$ their values just before time $0$ matter too, not only those for $t \ge 0$), and their derivatives satisfy $\varepsilon'(t) = \sigma'(t) / E + \sigma(t) / \eta$. If the strain is held at $\varepsilon(0)$ for every $t \ge 0$, then for every $t \ge 0$

$$\sigma(t) = \sigma(0)\, e^{-(E/\eta)\, t},$$

an exponential decay to zero with relaxation time $\tau = \eta / E$. Nothing is claimed for $t < 0$.

## Sources

- D. Roylance, *Engineering Viscoelasticity*, Massachusetts Institute of Technology (October 24, 2001), section 4.1, Example 2.
