# Linear shallow-water equations imply the wave equation

Let `η(t, x)` be the surface displacement and `u(t, x)` the velocity, with `H` and `g` real.
Suppose that at every `(t, x)`: the space slices of `η` and `u` are differentiable with
derivatives `ηₓ(t, x)` and `uₓ(t, x)`; the continuity equation `∂ₜη = -H uₓ` and the momentum
equation `∂ₜu = -g ηₓ` hold, the time slices being differentiable; the time slice of `uₓ` is
differentiable with derivative `∂ₓ∂ₜu`, so the mixed derivatives of `u` commute; and `ηₓ` is
differentiable in `x`. Then `∂ₜ∂ₜη = g H ∂ₓηₓ` at every `(t, x)`: `η` satisfies the wave
equation `∂ₜ²η = g H ∂ₓ²η`.
