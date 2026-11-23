# Wave eq of deriv system

Algebraic core of `shallow_water_wave_eq`, with the spatial partials written as Lean's
totalized `deriv`. If, for every `t, x`, `∂ₜη = -H ∂ₓu` and `∂ₜu = -g ∂ₓη` hold as `HasDerivAt`
statements for the time slices, the mixed-derivative commutation `∂ₜ∂ₓu = ∂ₓ∂ₜu` holds as a
`HasDerivAt` statement, and the second `x`-derivative of `η` is differentiable, then
`∂ₜ²η = g * H * ∂ₓ²η` at every `t, x`. Since `deriv` is `0` wherever a slice is not
differentiable, these hypotheses do not require `η t` or `u t` to be differentiable in `x`, so
they are not by themselves the shallow-water PDE; `shallow_water_wave_eq` adds that requirement.
