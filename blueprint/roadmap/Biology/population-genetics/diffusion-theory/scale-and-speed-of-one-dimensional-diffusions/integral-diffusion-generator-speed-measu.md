# Weak stationarity against the speed measure, boundary-flux form

Let `b`, `a` define a
[regular diffusion](../selection-duality-and-general-one-dimensional-di/is-regular-diffusion.md) on
`(0, 1)` (`a` positive and continuous on `(0, 1)`, `b / a` continuous on `(0, 1)` and integrable on
`[0, 1]`; accessibility of the endpoints and a probability normalization are not part of this), with
scale density `ψ` and [speed measure](speed-measure.md) `m`, and let `f` be twice continuously
differentiable on `[0, 1]`. Suppose that `f'(y) / ψ(y)` tends to `L₀` as `y → 0` from the right and
to `L₁` as `y → 1` from the left, and that `L_{b,a} f`, with `L_{b,a}` the
[backward generator](../selection-duality-and-general-one-dimensional-di/diffusion-generator.md), is
integrable with respect to `m`. Then

`∫ (L_{b,a} f) dm = L₁ - L₀`.

On `(0, 1)` the integrand times the speed density is the derivative `(f' / ψ)'`, by the
[canonical form](diffusion-generator-eq-one-div-speed-den.md) of the generator, so only the boundary
fluxes remain. The speed measure need not be finite.
