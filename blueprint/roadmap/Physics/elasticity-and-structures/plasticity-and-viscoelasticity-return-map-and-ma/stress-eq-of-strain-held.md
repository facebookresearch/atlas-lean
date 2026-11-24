# With strain held from t = 0, the Maxwell stress decays exponentially

Let a [Maxwell branch](maxwell-branch.md) with modulus $E > 0$ and viscosity $\eta > 0$ and
histories $\sigma$, $\varepsilon$ with rates $\sigma'$, $\varepsilon'$ obey the
[constitutive relation](is-history.md) on $[0, \infty)$, with two-sided derivatives at every
$t \ge 0$, $t = 0$ included, and let the strain be held: $\varepsilon(t) = \varepsilon(0)$ for every
$t \ge 0$. Then for every $t \ge 0$

$$\sigma(t) = \sigma(0)\, e^{-(E/\eta) t} = \sigma(0)\, e^{-t/\tau},$$

with $\tau = \eta / E$ the [relaxation time](relaxation-time.md): the stress relaxes exponentially
to $0$, since $E / \eta > 0$. Here $\sigma(0)$ is the stress at the start of the hold, after any
strain step; with $\sigma(0) = E\, \varepsilon(0)$ this is Maxwell's $F = E S e^{-t/T}$. Nothing is
claimed for $t < 0$.
