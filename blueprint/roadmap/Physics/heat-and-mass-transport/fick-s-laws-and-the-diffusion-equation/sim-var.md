# Sim Var

The similarity variable `ξ = x / √(Dt)`. It is meant for `D > 0` and `t > 0`; when
`D t ≤ 0` the square root is `0` and the value is `0` by Lean's division convention.
