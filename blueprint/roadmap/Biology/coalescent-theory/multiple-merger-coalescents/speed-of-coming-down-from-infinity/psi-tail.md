# The tail integral of 1/ψ

For a finite measure `Λ` on `[0, 1]` with [Laplace exponent](psi.md) `ψ` and a real `t`, the tail
integral is `u(t) = ∫_t^∞ dq / ψ(q)` (Berestycki–Berestycki–Limic, eq. (7)). The intended domain
is `t > 0` under [Grey's condition](grey-condition.md), where `u(t)` is finite and
[positive](psi-tail-pos.md). The definition is total: `1 / ψ(q)` is read as `0` where
`ψ(q) = 0`, and the integral is `0` when `q ↦ 1 / ψ(q)` is not integrable on `(t, ∞)`. Hence
`u ≡ 0` when Grey's condition fails, and `u(t) = 0` for `t ≤ 0` when `Λ ≠ 0`, since
`1 / ψ(q) ≥ 2 / (Λ([0, 1]) q²)` for `q > 0` is not integrable near `0`.
