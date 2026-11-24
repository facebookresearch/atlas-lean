# The lifetime is infinite iff the damage never reaches the threshold

For every damage path and threshold, with no continuity or monotonicity assumed, the
[lifetime](damage-lifetime.md) $\tau(\omega) = \inf\{u \ge 0 : d(\omega, u) \ge D(\omega)\}$ (or
$\infty$ if the threshold is never reached) is $\infty$ exactly when the damage stays strictly below
the threshold at every time:

$$\tau(\omega) = \infty \iff d(\omega, t) < D(\omega) \text{ for every } t \ge 0.$$
