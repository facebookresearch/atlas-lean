/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.SignedLDProfile
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open MeasureTheory Matrix MathlibExt.Biology.StatisticalGenetics.SignedLDProfile
open MathlibExt.Biology.StatisticalGenetics
open scoped ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.SignedLDProfile

/-- The uniform probability measure on `Fin 4`. -/
noncomputable def μ4 : Measure (Fin 4) := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ4 :=
  ⟨by simpa [μ4] using ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

/-- Integration against `μ4` is averaging over the four outcomes. -/
theorem integral_μ4 (f : Fin 4 → ℝ) : ∫ ω, f ω ∂μ4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  simp only [μ4, integral_smul_measure, integral_count, Fin.sum_univ_four]
  norm_num
  ring

/-- Three centred sign vectors on `Fin 4`. -/
noncomputable def s : Fin 3 → Fin 4 → ℝ :=
  ![![1, 1, -1, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]

/-- The witness: effects with mean `v = (1, 1)` (so `μ = 1`) and centred noise. -/
noncomputable def D : Model μ4 2 2 where
  meanBeta := ![1, 1]
  beta := ![fun ω => 1 + s 0 ω, fun ω => 1 + s 1 ω]
  eps := ![s 2, fun ω => -s 2 ω]
  integrable_beta := fun _ => Integrable.of_finite
  integrable_eps := fun _ => Integrable.of_finite
  integral_beta := by
    intro k
    fin_cases k <;> simp [integral_μ4, s] <;> norm_num
  integral_eps := by
    intro i
    fin_cases i <;> simp [integral_μ4, s]

/-- Two individuals, two markers in perfect LD. -/
def X2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; -1, -1]

theorem ldMatrix_X2 (j k : Fin 2) : ldMatrix X2 j k = 1 := by
  fin_cases j <;> fin_cases k <;> simp [ldMatrix, LDScore.ldCorr, X2, Fin.sum_univ_two]

/-- First-moment identity on the witness: the signed LD profile of `v = (1, 1)` under perfect LD
is `(2, 2)`, so `𝔼 α̂₀ = 2`. -/
example : ∫ ω, D.alphaHat X2 ω 0 ∂μ4 = 2 := by
  rw [D.integral_alphaHat_of_mean X2 (mu := 1) (v := ![1, 1]) (by simp [D]) 0]
  simp [mulVec, dotProduct, ldMatrix_X2, Fin.sum_univ_two]
  norm_num

/-- The same value by direct computation. -/
example : ∫ ω, D.alphaHat X2 ω 0 ∂μ4 = 2 := by
  simp [integral_μ4, Model.alphaHat, Model.pheno, D, X2, s, Fin.sum_univ_two]
  norm_num

/-- Unbiasedness of the unweighted (`W = 1`) estimator on the witness. -/
example : ∫ ω, (ldMatrix X2 *ᵥ ![1, 1]) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ D.alphaHat X2 ω) /
    ((ldMatrix X2 *ᵥ ![1, 1]) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ (ldMatrix X2 *ᵥ ![1, 1])))
      ∂μ4 = 1 :=
  D.integral_gls_estimator X2 (mu := 1) (by simp [D]) 1
    (by simp [mulVec, dotProduct, ldMatrix_X2, Fin.sum_univ_two])

/-- Junk value outside the domain: if the signed LD profile vanishes (`v = (1, -1)` under perfect
LD), the estimator's denominator is `0` and its value is `0` whatever `μ` is. -/
example : (ldMatrix X2 *ᵥ ![1, -1]) ⬝ᵥ (ldMatrix X2 *ᵥ ![1, -1]) = 0 := by
  simp [mulVec, dotProduct, ldMatrix_X2, Fin.sum_univ_two]

end MathlibExtTest.Biology.StatisticalGenetics.SignedLDProfile
