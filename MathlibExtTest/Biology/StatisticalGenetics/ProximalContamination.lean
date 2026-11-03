/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.ProximalContamination

@[expose] public section

open Matrix MathlibExt.Biology.StatisticalGenetics.ProximalContamination

namespace MathlibExtTest.Biology.StatisticalGenetics.ProximalContamination

/-! Two individuals, `V₀ = I`, candidate genotypes `x = (1, 1)`, phenotype `y = (1, 0)`,
`c = 1`: `xᵀ V₀⁻¹ x = 2`, `χ²(V₀) = 1 / 2`, and including the candidate divides it by
`1 + 2 = 3`. -/

/-- The candidate marker. -/
def x : Fin 2 → ℝ := ![1, 1]

/-- The phenotype. -/
def y : Fin 2 → ℝ := ![1, 0]

example : mmChiSq (1 : Matrix (Fin 2) (Fin 2) ℝ) x y = 1 / 2 := by
  simp [mmChiSq, x, y, dotProduct, Fin.sum_univ_two]
  norm_num

/-- The contaminated statistic, via the theorem: `(1/2) / 3 = 1/6`. -/
example : mmChiSq (1 + (1 : ℝ) • vecMulVec x x) x y = 1 / 6 := by
  rw [mmChiSq_add_smul_vecMulVec PosDef.one zero_le_one]
  simp [mmChiSq, x, y, dotProduct, Fin.sum_univ_two]
  norm_num

/-- The Sherman–Morrison step on the example: `(I + x xᵀ)⁻¹ x = x / 3`. -/
example : (1 + (1 : ℝ) • vecMulVec x x)⁻¹ *ᵥ x = (3 : ℝ)⁻¹ • x := by
  rw [inv_add_smul_vecMulVec_mulVec PosDef.one zero_le_one]
  simp [x, dotProduct, Fin.sum_univ_two]
  norm_num

/-- Boundary `c = 0`: no contamination, no change. -/
example (V₀ : Matrix (Fin 2) (Fin 2) ℝ) (y' : Fin 2 → ℝ) :
    mmChiSq (V₀ + (0 : ℝ) • vecMulVec x x) x y' = mmChiSq V₀ x y' := by
  simp

/-- The deflation never increases the statistic. -/
example : mmChiSq (1 + (1 : ℝ) • vecMulVec x x) x y ≤ mmChiSq 1 x y :=
  mmChiSq_add_smul_vecMulVec_le PosDef.one zero_le_one x y

end MathlibExtTest.Biology.StatisticalGenetics.ProximalContamination
