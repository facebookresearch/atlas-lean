# Birkhoff limit of an ergodic map is the space average

Let $\mu$ be a probability measure on $X$, $T : X \to X$ an ergodic map for $\mu$ (in particular $T$ is measurable
and preserves $\mu$), and $f : X \to \mathbb{R}$ an integrable function. Then the [Birkhoff limit](birkhoff-limit.md)
of $f$ is the constant $\int f \, d\mu$ almost everywhere:

$$\bar f(x) = \int f \, d\mu \quad \text{for } \mu\text{-almost every } x.$$

It combines the [ergodic case of Birkhoff's theorem](birkhoff-pointwise-ergodic.md) with the
[almost-everywhere convergence to the Birkhoff limit](tendsto-birkhoff-average-ae.md).
