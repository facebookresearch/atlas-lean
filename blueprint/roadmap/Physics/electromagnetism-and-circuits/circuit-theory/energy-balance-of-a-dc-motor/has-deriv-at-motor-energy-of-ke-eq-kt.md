# Energy balance of a DC motor with equal motor constants

Let `R`, `L`, `J`, `b` and `ke = kt` be real numbers, `u, i, ω, τL : ℝ → ℝ` functions of time, and
`t` a time at which `i` and `ω` are differentiable and the armature and rotor equations
`u = R i + L i' + ke ω` and `J ω' = kt i - b ω - τL` hold. Then the [stored energy](motor-energy.md)
has derivative `u i - R i² - b ω² - τL ω` at `t`. The premise `ke = kt` holds for the motor
constants in coherent SI units; it is an assumption, not a consequence of the equations.
