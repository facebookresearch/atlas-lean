# Entire solutions of Briot–Bouquet equations in the remaining normal form

Remaining Briot–Bouquet data from (Eremenko, remaining 2024
case): order `k` with `2 ≤ k`, degree `d` with `1 ≤ d`, governing polynomial
`F : MvPolynomial (Fin 2) ℂ` with `totalDegree F = d`, `Irreducible F`,
remaining normal form `F = (X₀ - a * X₁) ^ d + Q`, lower part
`Q : MvPolynomial (Fin 2) ℂ` with `Q.totalDegree ≤ d - 1`, entire `f`
(`Differentiable ℂ f`) satisfying both `eval F = 0` and the normal-form
equation `((iteratedDeriv k f z - a * f z) ^ d + eval Q = 0)` for all `z`,
with `X₀ ↦ iteratedDeriv k f z` and `X₁ ↦ f z`.
