# Work of minus a gradient in a Hilbert space is the potential drop

Let `E` be a complete real inner product space, `U : E → ℝ` a potential with gradient `g(x)` at
every `x`, and `F = -g`. Let `γ, γ' : ℝ → E` and real `a`, `b` be such that `γ` has derivative
`γ'(t)` at every `t` between `a` and `b` (in either order, ends included), and suppose the work
integrand `t ↦ ⟨F(γ(t)), γ'(t)⟩` is integrable on that interval. Then

`∫ₐᵇ ⟨F(γ(t)), γ'(t)⟩ dt = -(U(γ(b)) - U(γ(a)))`.

Completeness is needed only to speak of the gradient; with the derivative of `U` represented by
`g` as `w ↦ ⟨g(x), w⟩`, the identity holds in every real inner product space
([general form](conservative-force-work-eq-potential-dec.md)).
