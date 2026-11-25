# Lifetime as the hitting time of the damage threshold

Let $\Omega$ be a set of outcomes, and for $\omega \in \Omega$ let $t \mapsto d(\omega, t)$, for
times $t \in [0, \infty)$, be a real damage path and $D(\omega)$ a real threshold. The lifetime of
the component is the hitting time of $d - D$ into $[0, \infty)$ from time $0$:

$$\tau(\omega) = \inf\{t \ge 0 : d(\omega, t) \ge D(\omega)\} \in [0, \infty],$$

with $\tau(\omega) = \infty$ when the set is empty, that is, when the threshold is never reached.
The definition does not require the infimum to be attained. For a continuous nondecreasing path
$t \mapsto d(\omega, t)$,
[$t < \tau(\omega)$ exactly when $d(\omega, t) < D(\omega)$](lt-damage-lifetime-iff.md), and
[$\tau(\omega) \le t$ exactly when $d(\omega, t) \ge D(\omega)$](damage-lifetime-le-iff.md), for
every time $t \ge 0$.
