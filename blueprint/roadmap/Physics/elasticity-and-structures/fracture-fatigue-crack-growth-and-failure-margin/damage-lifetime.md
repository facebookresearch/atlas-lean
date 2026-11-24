# Lifetime as the hitting time of the damage threshold

Let $\Omega$ be a set of outcomes, and for $\omega \in \Omega$ let $t \mapsto d(\omega, t)$, for
times $t \in [0, \infty)$, be a real damage path and $D(\omega)$ a real threshold. The lifetime of
the component is the hitting time of $d - D$ into $[0, \infty)$ from time $0$:

$$\tau(\omega) = \inf\{t \ge 0 : d(\omega, t) \ge D(\omega)\} \in [0, \infty],$$

with $\tau(\omega) = \infty$ when the set is empty, that is, when the threshold is never reached.
For a general path the infimum need not be attained; for a
[continuous nondecreasing path](lt-damage-lifetime-iff.md) it is.
