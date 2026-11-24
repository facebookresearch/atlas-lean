# For continuous nondecreasing damage, failure by $t$ is failure at $t$

If the damage path $u \mapsto d(\omega, u)$ is continuous and nondecreasing on $[0, \infty)$, then
for every finite time $t \ge 0$ the [lifetime](damage-lifetime.md)
$\tau(\omega) = \inf\{u \ge 0 : d(\omega, u) \ge D(\omega)\}$ (or $\infty$ if the threshold is never
reached) satisfies

$$\tau(\omega) \le t \iff D(\omega) \le d(\omega, t),$$

the [failure event](demand-failure.md) at $t$; equality with the threshold counts as failure.
