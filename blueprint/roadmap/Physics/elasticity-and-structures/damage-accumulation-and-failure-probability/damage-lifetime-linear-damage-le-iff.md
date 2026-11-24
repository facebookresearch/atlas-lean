# For a nonnegative rate, failure by time t is exactly D ≤ d0 + r t

For a scenario $\omega$ with rate $r(\omega) \ge 0$, any initial damage $d_0(\omega)$, any threshold
$D(\omega)$ and every time $t \ge 0$, the
[lifetime](../fracture-fatigue-crack-growth-and-failure-margin/damage-lifetime.md) $\tau(\omega)$ of
the [linear damage path](linear-damage.md) $d_0(\omega) + r(\omega)\, s$ against $D(\omega)$
satisfies

$$\tau(\omega) \le t \iff D(\omega) \le d_0(\omega) + r(\omega)\, t:$$

the component has failed by time $t$ exactly when its damage at $t$ has reached the threshold,
equality included. A zero rate is allowed: the lifetime is then $0$ if $D(\omega) \le d_0(\omega)$
and $\infty$ otherwise.
