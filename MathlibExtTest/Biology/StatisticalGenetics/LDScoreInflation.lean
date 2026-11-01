/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScoreInflation

@[expose] public section

open MeasureTheory MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
open scoped ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.LDScoreInflation

/-! ### A mean-zero witness model

`N = 2` individuals, `M = 1` marker, `h² = 9/25`, on `Fin 4` with the uniform probability
measure: the effect is `(6/5) h₁` and the noise terms are `(8/5) h₂`, `(8/5) h₃` for the
mean-zero orthogonal sign vectors `hᵢ / 2` (second moment `1/4`), so `𝔼[β²] = 9/25 = h² / M`
and `𝔼[ε²] = 16/25 = 1 - h²`. -/

/-- The uniform probability measure on `Fin 4`. -/
noncomputable def μ4 : Measure (Fin 4) := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ4 :=
  ⟨by simpa [μ4] using ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

theorem integral_μ4 (f : Fin 4 → ℝ) : ∫ ω, f ω ∂μ4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  simp only [μ4, integral_smul_measure, integral_count, Fin.sum_univ_four]
  norm_num
  ring

/-- Mean-zero sign vectors of length `4`, scaled by `1/2`. -/
noncomputable def had : Fin 3 → Fin 4 → ℝ :=
  ![![1/2, 1/2, -1/2, -1/2], ![1/2, -1/2, 1/2, -1/2], ![1/2, -1/2, -1/2, 1/2]]

/-- The witness model. -/
noncomputable def D : Model μ4 2 1 where
  h2 := 9 / 25
  beta := fun _ ω => 6 / 5 * had 0 ω
  eps := ![fun ω => 8 / 5 * had 1 ω, fun ω => 8 / 5 * had 2 ω]
  memLp_beta := fun _ => MemLp.of_discrete
  memLp_eps := fun _ => MemLp.of_discrete
  integral_beta_mul := by
    intro k l
    simp [Subsingleton.elim k l, integral_μ4, had]
    norm_num
  integral_eps_mul := by
    intro i i'
    fin_cases i <;> fin_cases i' <;> simp [integral_μ4, had] <;> norm_num
  integral_beta_mul_eps := by
    intro k i
    fin_cases i <;> simp [integral_μ4, had] <;> norm_num

theorem hβ : ∀ k, ∫ ω, D.beta k ω ∂μ4 = 0 := fun _ => by
  simp [D, integral_μ4, had]
  norm_num

theorem hε : ∀ i, ∫ ω, D.eps i ω ∂μ4 = 0 := fun i => by
  fin_cases i <;> simp [D, integral_μ4, had] <;> norm_num

/-- One marker, standardized: the column `(1, -1)`. -/
def X : Matrix (Fin 2) (Fin 1) ℝ := !![1; -1]

theorem isStandardized_X : IsStandardized X := by
  intro k
  fin_cases k
  simp [X, Fin.sum_univ_two]
  norm_num

theorem ldScore_X : ldScore X 0 = 1 := by
  simp [ldScore, ldCorr, X, Fin.sum_univ_two]

/-- Polygenic inflation: mean `𝔼[χ²] = 1 - 9/25 + 2 (9/25) · 1 = 34/25`. -/
example : (∑ j, ∫ ω, D.chiSq X j ω ∂μ4) / ((1 : ℕ) : ℝ) = 34 / 25 := by
  rw [mean_integral_chiSq D X two_ne_zero one_ne_zero isStandardized_X]
  simp [meanLDScore, ldScore_X, D]
  norm_num

/-- Stratification along the axis `c = (1, 0)` with `s = 1`: `X_jᵀ c / N = 1/2`, so the extra
term is `N s² (1/2)² = 1/2` and `𝔼[χ²] = 18/25 + 16/25 + 1/2 = 93/50`. -/
example : ∫ ω, chiSqStrat D X 1 ![1, 0] 0 ω ∂μ4 = 93 / 50 := by
  rw [integral_chiSqStrat_of_standardized D X two_ne_zero isStandardized_X hβ hε, ldScore_X]
  simp [D, X, Fin.sum_univ_two]
  norm_num

/-- The same value by direct computation of the expectation. -/
example : ∫ ω, chiSqStrat D X 1 ![1, 0] 0 ω ∂μ4 = 93 / 50 := by
  simp [integral_μ4, chiSqStrat, betaHatStrat, phenoStrat, Model.pheno, D, X, had,
    Fin.sum_univ_two]
  norm_num

/-- With a single marker the stratification term is constant (`a = 1/4`); the attenuation
ratio of the exact intercept `1 - h² + N a = 57/50` is `(1/2 - 9/25) / (43/50) = 7/43`. -/
example : attenuationRatio (1 - D.h2 + ((2 : ℕ) : ℝ) * (1 / 4))
    ((∑ j, ∫ ω, chiSqStrat D X 1 ![1, 0] j ω ∂μ4) / ((1 : ℕ) : ℝ)) = 7 / 43 := by
  have h := attenuationRatio_of_const D X two_ne_zero one_ne_zero isStandardized_X hβ hε 1
    ![1, 0] (a := 1 / 4) (fun j => by fin_cases j; simp [X, Fin.sum_univ_two]; norm_num)
  rw [h]
  simp [meanLDScore, ldScore_X, D]
  norm_num

/-- The confounding share above the exact null level: `(1/2) / (1/2 + 18/25) = 25/61`. -/
example : ((1 - D.h2 + ((2 : ℕ) : ℝ) * (1 / 4)) - (1 - D.h2)) /
    ((∑ j, ∫ ω, chiSqStrat D X 1 ![1, 0] j ω ∂μ4) / ((1 : ℕ) : ℝ) - (1 - D.h2)) = 25 / 61 := by
  have h := confoundingShare_of_const D X two_ne_zero one_ne_zero isStandardized_X hβ hε 1
    ![1, 0] (a := 1 / 4) (fun j => by fin_cases j; simp [X, Fin.sum_univ_two]; norm_num)
  rw [h]
  simp [meanLDScore, ldScore_X, D]
  norm_num

example : (2 : ℕ) * (1 / 4 : ℝ) / (2 * (1 / 4) + 2 * (9 / 25) / (1 : ℕ) * 1) ∈ Set.Icc 0 1 :=
  confoundingShare_mem_Icc (by norm_num) (by norm_num) (by norm_num)

/-- Boundary: without stratification (`s = 0`) the identity reduces to `LDScore`'s. -/
example : ∫ ω, chiSqStrat D X 0 ![1, 0] 0 ω ∂μ4 = ∫ ω, D.chiSq X 0 ω ∂μ4 := by
  rw [integral_chiSqStrat_of_standardized D X two_ne_zero isStandardized_X hβ hε,
    D.integral_chiSq_of_standardized X two_ne_zero 0 isStandardized_X]
  simp

#print axioms integral_chiSqStrat
#print axioms mean_integral_chiSq
#print axioms attenuationRatio_of_const

end MathlibExtTest.Biology.StatisticalGenetics.LDScoreInflation
