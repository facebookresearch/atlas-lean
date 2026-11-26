# For continuous nondecreasing damage, up at $t$ iff below threshold

If the damage path $u \mapsto d(\omega, u)$ is continuous and nondecreasing on $[0, \infty)$, then
for every finite time $t \ge 0$ the [lifetime](damage-lifetime.md)
$\tau(\omega) = \inf\{u \ge 0 : d(\omega, u) \ge D(\omega)\}$ (or $\infty$ if the threshold is never
reached) satisfies

$$t < \tau(\omega) \iff d(\omega, t) < D(\omega):$$

the component is up at $t$ exactly when its damage is still below the threshold. Continuity
matters: for the nondecreasing, discontinuous path with $d(u) = 0$ for $u \le 1$ and $d(u) = 1$
for $u > 1$, and threshold $1$, the lifetime is $1$ although $d(1) < 1$.
