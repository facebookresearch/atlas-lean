# Local well-posedness of the Turing system

**Local well-posedness of the Turing system** in `C(K, ℝ²)`. Let `H` be a C₀ semigroup on
`C(K, ℝ)` with generator `A`, let `d_u, d_v ≥ 0`, and let the kinetics `f : ℝ² → ℝ²` be `C¹`.
For every radius `r` there are a time `T > 0`, a bound `R`, a constant `C ≥ 0` and a solution map
`sol` such that for `‖x₀‖ ≤ r`, `sol x₀` is a continuous mild solution on `[0, T]` of
`w_t = D A w + f(w)`, `w 0 = x₀`, bounded by `R`, and `‖sol x₀ t - sol y₀ t‖ ≤ C ‖x₀ - y₀‖` on
`[0, T]` for `‖x₀‖, ‖y₀‖ ≤ r`. This is the Neumann problem `w_t = D Δ_N w + f(w)` exactly when
`H` is the Neumann heat semigroup `e^{τ Δ_N}`.
