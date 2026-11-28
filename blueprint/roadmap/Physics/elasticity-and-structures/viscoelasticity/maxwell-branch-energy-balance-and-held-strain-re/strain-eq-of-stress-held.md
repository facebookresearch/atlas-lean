# Creep of a Maxwell branch under constant stress

Let a Maxwell branch have modulus $E > 0$ and viscosity $\eta > 0$, and let stress and strain histories $\sigma$ and $\varepsilon$ obey [the constitutive relation](is-history.md) on $[0, \infty)$. That is, at every $t \ge 0$, including $t = 0$, both histories are differentiable at $t$ in the ordinary two-sided sense (so at $t = 0$ their values just before time $0$ matter too, not only those for $t \ge 0$), and their derivatives satisfy $\varepsilon'(t) = \sigma'(t) / E + \sigma(t) / \eta$. If the stress is held at $\sigma(0)$ for every $t \ge 0$, then for every $t \ge 0$

$$\varepsilon(t) = \varepsilon(0) + \frac{\sigma(0)}{\eta}\, t,$$

so for $\sigma(0) \ne 0$ the branch creeps without bound. Nothing is claimed for $t < 0$.
