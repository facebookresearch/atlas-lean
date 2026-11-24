# Time-map expansion from a Hölder-differentiable reaction

**Time-map expansion from a Hölder-differentiable reaction** (the differentiability input
of linearized instability, in the PDE-01 mild formulation).

Let `SA` be a C₀ semigroup on a real Banach space `X` (for the Turing system, the Neumann heat
semigroup `e^{t D Δ_N}` on `C(Ω̄; ℝ²)`) and `F` a reaction term that is Lipschitz on bounded sets.
Let `u₀` be an equilibrium: `SA t u₀ = u₀` (a homogeneous state is fixed by the Neumann heat
semigroup) and `F u₀ = 0`. Suppose `F` is differentiable at `u₀` with a Hölder remainder:
`‖F (u₀ + z) - F u₀ - B z‖ ≤ K ‖z‖ᵖ` for `‖z‖ ≤ r`. Let `S` be the linearized semigroup, i.e.
`t ↦ S t y` is the mild solution of `w' = A w + B w`, `w 0 = y`. Let `Φ` be the nonlinear flow on
`[0, T]` from the ball `‖x - u₀‖ ≤ ρ₀`, bounded by `R` there. Then the time-`T` map satisfies
`‖Φ T (u₀ + y) - u₀ - S T y‖ ≤ C ‖y‖ᵖ` for `‖y‖ ≤ ρ`, for some `ρ > 0` and `C ≥ 0`.

The proof writes the error `e t = Φ t x - u₀ - S t y` as a Duhamel integral of
`F (Φ s x) - B (S s y) = [Hölder remainder] + B (e s)`, bounds `‖Φ s x - u₀‖` by Lipschitz
dependence on initial data (`exists_norm_sub_le_of_norm_le`) and closes with Grönwall.
