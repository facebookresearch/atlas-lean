# Constitutive relation of a Maxwell branch

For a Maxwell branch with modulus $E$ and viscosity $\eta$, a stress history $\sigma$ and a strain history $\varepsilon$, both real functions of time defined on all of $\mathbb{R}$, obey the constitutive relation on a time set $I$ when, at every $t \in I$, $\sigma$ and $\varepsilon$ are differentiable at $t$ in the ordinary two-sided sense, with derivatives $\sigma'(t)$ and $\varepsilon'(t)$, and the strain rate is the spring strain rate plus the dashpot strain rate:

$$\varepsilon'(t) = \frac{\sigma'(t)}{E} + \frac{\sigma(t)}{\eta}.$$

The rates $\sigma'$ and $\varepsilon'$ are the actual derivatives, not arbitrary supplied rates. When $I$ has an endpoint, such as $I = [0, \infty)$, the derivative there is still two-sided, so the histories must be defined and differentiable on both sides of it; a one-sided (right) derivative at $t = 0$ is not enough.
