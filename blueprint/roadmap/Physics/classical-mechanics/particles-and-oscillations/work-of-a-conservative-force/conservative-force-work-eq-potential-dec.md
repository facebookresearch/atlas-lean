# Work of a conservative force equals the potential decrease

Let `E` be a real inner product space, `U : E → ℝ` a potential and `g, F : E → E` vector fields
with `F(x) = -g(x)` for every `x`, where at every `x` the derivative of `U` is the linear map
`w ↦ ⟨g(x), w⟩` (so `g` represents the derivative of `U`; `E` need not be complete). Let
`γ, γ' : ℝ → E` and real `a`, `b` be such that `γ` has derivative `γ'(t)` at every `t` between `a`
and `b` (in either order, ends included), and suppose the work integrand `t ↦ ⟨F(γ(t)), γ'(t)⟩` is
integrable on that interval. Then

`∫ₐᵇ ⟨F(γ(t)), γ'(t)⟩ dt = -(U(γ(b)) - U(γ(a)))`:

the work of `F` along the path is the decrease of the potential. The integral is oriented, so the
identity also holds for `a > b`. In the physical reading `E` is the space of positions, `F` a
conservative force and `U` its potential energy.
