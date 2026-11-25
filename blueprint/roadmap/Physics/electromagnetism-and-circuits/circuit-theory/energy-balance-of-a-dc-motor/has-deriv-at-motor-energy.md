# Energy identity of a DC motor

Let `R`, `L`, `J`, `b`, `ke` and `kt` be real numbers, `u, i, ω, τL : ℝ → ℝ` functions of time, and
`t` a time at which `i` and `ω` are differentiable and the armature equation `u = R i + L i' + ke ω`
and the rotor equation `J ω' = kt i - b ω - τL` hold. Then the [stored energy](motor-energy.md)
`E = L i² / 2 + J ω² / 2` has derivative `u i - R i² - b ω² - τL ω + (kt - ke) i ω` at `t`. No sign
condition on the parameters is used; the load torque `τL` is counted positive when it opposes
positive rotation.
