# The Maxwell constitutive relation in relaxation form

For a [Maxwell branch](maxwell-branch.md) with modulus $E > 0$ and viscosity $\eta > 0$, every set
$I$ of times and all real functions $\sigma$, $\sigma'$, $\varepsilon$, $\varepsilon'$, the
histories obey the [constitutive relation](is-history.md) on $I$ if and only if at every $t \in I$,
$\sigma$ has the two-sided derivative $\sigma'(t)$, $\varepsilon$ has the two-sided derivative
$\varepsilon'(t)$, and

$$\sigma'(t) + \frac{\sigma(t)}{\tau} = E\, \varepsilon'(t),$$

with $\tau = \eta / E$ the [relaxation time](relaxation-time.md). This is Maxwell's
$dF/dt = E\, dS/dt - F/T$ with time of relaxation $T = \tau$. The equivalence uses $E \ne 0$.
