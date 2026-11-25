# Error bound normalized by the initial concentration

Pseudo-first-order error normalized by the initial concentration `[A]₀`: for `0 < [A]₀ < [B]₀`,
`k > 0` and `t ≥ 0`, `|c_A(t) - [A]₀ exp(-k[B]₀t)| / [A]₀ ≤ r (1 / (1 - r) + k[B]₀t)` with
`r = [A]₀ / [B]₀`, where `c_A(t)` is the concentration of `A` at time `t` given by the
[integrated A + B → P law for A](second-order-absol-a.md). The denominator is `[A]₀`, not the concentration at
time `t`, so this is not a relative error at time `t`.
