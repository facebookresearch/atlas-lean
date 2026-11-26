# With a nonzero coupling residual the reciprocal balance fails

Let `R`, `L`, `J`, `b`, `ke` and `kt` be real numbers, `u, i, ω, τL : ℝ → ℝ` functions of time, and
`t` a time at which `i` and `ω` are differentiable, the armature and rotor equations
`u = R i + L i' + ke ω` and `J ω' = kt i - b ω - τL` hold, and `(kt - ke) i ω ≠ 0`. Then the
derivative of the [stored energy](motor-energy.md) at `t` differs from
`u i - R i² - b ω² - τL ω`.
