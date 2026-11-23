# Shallow water wave eq

Linear 1D shallow water implies the wave equation. Suppose that, for every `t, x`, the
space slices of `η` and `u` have derivatives `ηx t x` and `ux t x` (as `HasDerivAt` statements),
the continuity equation `∂ₜη = -H ∂ₓu` and the momentum equation `∂ₜu = -g ∂ₓη` hold (as
`HasDerivAt` statements for the time slices), the mixed-derivative commutation `∂ₜ∂ₓu = ∂ₓ∂ₜu`
holds (as a `HasDerivAt` statement), and `ηx t` is differentiable. Then
`∂ₜ²η = g * H * ∂ₓ²η` at every `t, x`, where `deriv (fun s => η s x) t` is `∂ₜη(t, x)` and
`deriv (fun x' => ηx t x') x` is `∂ₓ²η(t, x)`.
