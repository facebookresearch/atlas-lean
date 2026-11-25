# Well-posedness of radiative transfer in a scattering gray slab

This node covers the plane-parallel radiative transfer equation with isotropic scattering. Let $\tau_0 > 0$, $\omega \in [0, 1)$, let
$I_b$ be bounded and measurable on $[0, \tau_0]$, and let the incoming intensities $I^-(\mu)$ for $\mu > 0$ at $\tau = 0$ and $I^+(\mu)$ for
$\mu < 0$ at $\tau = \tau_0$ be bounded and measurable. Then there is exactly one $I \in L^\infty([0, \tau_0] \times [-1, 1])$, up to
equality almost everywhere, such that for almost every $\mu \ne 0$ the function $\tau \mapsto I(\tau, \mu)$ is absolutely continuous and
satisfies, for almost every $\tau$,

$$\mu\,\frac{\partial I}{\partial\tau} + I = (1 - \omega)I_b(\tau) + \frac{\omega}{2}\int_{-1}^{1} I(\tau, \mu')\,d\mu',$$

with $I(0, \mu) = I^-(\mu)$ for almost every $\mu > 0$ and $I(\tau_0, \mu) = I^+(\mu)$ for almost every $\mu < 0$. The source iteration that solves the transport equation with the previous iterate in the scattering integral
converges to it in $L^\infty$, with error decreasing at least by the factor $\omega$ per step.

## Expansion

A good expansion writes the solution of the transport equation with a given source along characteristics, shows that this map
followed by angular averaging has sup-norm at most one, and concludes by the Banach fixed-point theorem. Nongray media, anisotropic scattering
and coupling to the energy equation are separate nodes.

## Sources

- M. F. Modest, *Radiative Heat Transfer*, 3rd edition, Academic Press, 2013, for the radiative transfer equation in participating media.
