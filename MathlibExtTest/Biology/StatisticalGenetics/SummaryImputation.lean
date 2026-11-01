/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.SummaryImputation
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open MeasureTheory Matrix MathlibExt.Biology.StatisticalGenetics.SummaryImputation
open scoped ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.SummaryImputation

/-- The uniform probability measure on `Fin 4`. -/
noncomputable def μ4 : Measure (Fin 4) := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ4 :=
  ⟨by simpa [μ4] using ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

/-- Integration against `μ4` is averaging over the four outcomes. -/
theorem integral_μ4 (f : Fin 4 → ℝ) : ∫ ω, f ω ∂μ4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  simp only [μ4, integral_smul_measure, integral_count, Fin.sum_univ_four]
  norm_num
  ring

/-- Three orthonormal centred sign vectors on `Fin 4`. -/
noncomputable def s : Fin 3 → Fin 4 → ℝ :=
  ![![1, 1, -1, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]

/-- The witness: typed statistics `z₁ = s₀`, `z₂ = s₀ + s₁`, target
`z_t = s₀ + s₂`: `Σ_oo = [[1, 1], [1, 2]]`, `Σ_ot = (1, 1)`, `Σ_tt = 2`. -/
noncomputable def D : Model μ4 (Fin 2) where
  zt := fun ω => s 0 ω + s 2 ω
  zo := ![s 0, fun ω => s 0 ω + s 1 ω]
  memLp_zt := MemLp.of_discrete
  memLp_zo := fun _ => MemLp.of_discrete
  sigmaOO := !![1, 1; 1, 2]
  sigmaOT := ![1, 1]
  sigmaTT := 2
  integral_zo_mul := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [integral_μ4, s] <;> norm_num
  integral_zt_mul := by
    intro i
    fin_cases i <;> simp [integral_μ4, s] <;> norm_num
  integral_zt_sq := by
    simp [integral_μ4, s]
    norm_num

/-- The ImpG weights solve `Σ_oo w = Σ_ot`: `w = (1, 0)`. -/
theorem normal_w : D.sigmaOO *ᵥ ![1, 0] = D.sigmaOT := by
  ext i
  fin_cases i <;> simp [D, mulVec, dotProduct, Fin.sum_univ_two]

/-- `r²_pred = wᵀ Σ_ot = 1`. -/
example : ∫ ω, D.imputed ![1, 0] ω ^ 2 ∂μ4 = 1 := by
  rw [D.integral_imputed_sq_of_normal normal_w]
  simp [D, dotProduct, Fin.sum_univ_two]

/-- Conditional variance `Σ_tt - wᵀ Σ_ot = 1`. -/
example : ∫ ω, (D.zt ω - D.imputed ![1, 0] ω) ^ 2 ∂μ4 = 1 := by
  rw [D.integral_error_sq_of_normal normal_w]
  simp [D, dotProduct, Fin.sum_univ_two]
  norm_num

/-- The same conditional variance by direct computation. -/
example : ∫ ω, (D.zt ω - D.imputed ![1, 0] ω) ^ 2 ∂μ4 = 1 := by
  simp [integral_μ4, Model.imputed, D, s, Fin.sum_univ_two]
  norm_num

/-- Another linear imputation, `w' = (0, 1/2)`, does worse: excess `(w' - w)ᵀ Σ_oo (w' - w)`. -/
example : ∫ ω, (D.zt ω - D.imputed ![1, 0] ω) ^ 2 ∂μ4 ≤
    ∫ ω, (D.zt ω - D.imputed ![0, 1 / 2] ω) ^ 2 ∂μ4 :=
  D.integral_error_sq_le normal_w _

/-- Ridge weights with `λ = 1`: `(Σ_oo + I) w = Σ_ot` gives `w = (2/5, 1/5)`, whose null second
moment is `wᵀ Σ_oo w = 2/5`, not `wᵀ Σ_ot = 3/5`; normalizing by `√(2/5)` gives second moment
`1`. -/
example : (D.sigmaOO + 1) *ᵥ ![2 / 5, 1 / 5] = D.sigmaOT ∧
    ![2 / 5, 1 / 5] ⬝ᵥ (D.sigmaOO *ᵥ ![2 / 5, 1 / 5]) = 2 / 5 := by
  constructor
  · ext i
    fin_cases i <;> simp [D, mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · simp [D, mulVec, dotProduct, Fin.sum_univ_two]
    norm_num

example : ∫ ω, (D.imputed ![2 / 5, 1 / 5] ω /
    Real.sqrt (![2 / 5, 1 / 5] ⬝ᵥ (D.sigmaOO *ᵥ ![2 / 5, 1 / 5]))) ^ 2 ∂μ4 = 1 :=
  D.integral_normalized_sq _ (by simp [D, mulVec, dotProduct, Fin.sum_univ_two]; norm_num)

end MathlibExtTest.Biology.StatisticalGenetics.SummaryImputation
