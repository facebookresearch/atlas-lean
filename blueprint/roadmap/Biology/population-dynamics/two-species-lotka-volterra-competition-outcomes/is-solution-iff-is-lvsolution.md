# The competition equations as a Lotka–Volterra system

`z` solves the competition
equations (`IsSolution`) exactly when the curve `t ↦ ![(z t).1, (z t).2]` in `Fin 2 → ℝ` solves
the Lotka–Volterra system `yᵢ' = yᵢ (rᵢ + ∑ⱼ Cᵢⱼ yⱼ)` (`IsLVSolution`, with the library's field
`lvField`) for growth rates `(r₁, r₂)` and the interaction matrix `C` with rows
`(-r₁ / K₁, -r₁ α₁₂ / K₁)` and `(-r₂ α₂₁ / K₂, -r₂ / K₂)`. Both predicates ask for two-sided
derivatives at every time `t ≥ 0`, so results stated for `IsLVSolution` apply to the competition
model.
