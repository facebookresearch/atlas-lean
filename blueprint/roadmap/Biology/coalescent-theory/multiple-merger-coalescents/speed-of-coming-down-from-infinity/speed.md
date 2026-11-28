# The speed of coming down from infinity

For a finite measure `Λ` on `[0, 1]` and a real `t`, the speed of coming down from infinity is
`v(t) = inf {s > 0 : u(s) < t}`, where `u(s) = ∫_s^∞ dq / ψ(q)` is the
[tail integral](psi-tail.md) of the [Laplace exponent](psi.md) `ψ`
(Berestycki–Berestycki–Limic, eq. (8)). The infimum of the empty set is read as `0`, so
`v(t) = 0` for `t ≤ 0`, as `u ≥ 0`. Under [Grey's condition](grey-condition.md) and for `t > 0`,
`v(t) > 0` and [`u(v(t)) = t`](psi-tail-speed.md); when Grey's condition fails, `u ≡ 0` and
`v ≡ 0`.
