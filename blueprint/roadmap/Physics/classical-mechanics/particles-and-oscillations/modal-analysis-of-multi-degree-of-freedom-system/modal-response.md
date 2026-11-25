# Modal response in physical coordinates

Let `n` be a finite set of degrees of freedom, `C` a real `n × n` matrix, `μ : n → ℝ` and
`x₀, v₀ ∈ ℝⁿ`. The modal response at time `t` is

`x(t) = C q(t)`, with `q_i(t)` the [modal response](modal-coordinate.md) for the entry `μ_i`
starting from `(C⁻¹ x₀)_i` with velocity `(C⁻¹ v₀)_i`.

`C⁻¹` is the matrix inverse, taken to be the zero matrix when `C` is not invertible; for a
mass-orthonormal `C` it is `Cᵀ M` ([inverse](inv-eq-transpose-mul.md)).
