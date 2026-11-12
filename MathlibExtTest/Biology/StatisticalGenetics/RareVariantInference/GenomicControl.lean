/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.RareVariantInference.GenomicControl

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
  MathlibExt.Biology.StatisticalGenetics.RareVariantInference.GenomicControl
open scoped NNReal ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.RareVariantInference.GenomicControl

/-! ### API-00 smoke test: the reused and new names resolve and compose -/

example : chiSqOneTail 1 < chiSqOneTail 0 := chiSqOneTail_lt_of_lt le_rfl one_pos

example (D : Model (Measure.dirac ()) 1 1) (X : Matrix (Fin 1) (Fin 1) ℝ) :
    lambdaGC D X 0 0 = (∑ j, ∫ ω, chiSqStrat D X 0 0 j ω ∂(Measure.dirac ())) / (1 : ℕ) :=
  rfl

/-! ### Gaussian rescaling under an exact distributional hypothesis

The single score is the identity on `ℝ` under `𝒩(0, 2)`, so its assumed variance is `λ = 2`.
This witness supplies a Gaussian law directly; it does not model population structure. -/

/-- A single Gaussian score with variance `λ = 2`. -/
noncomputable def G2 : CommonInflationModel (gaussianReal 0 2) Unit where
  lam := 2
  lam_ne_zero := two_ne_zero
  score := fun _ => id
  hasLaw_score := fun _ => HasLaw.id

/-- Calibrated: `P(χ² / 2 > c)` is the `χ²₁` tail at `c`, for every threshold. -/
example (c : ℝ) : gaussianReal 0 2 {x | c < x ^ 2 / 2} = chiSqOneTail c := by
  simpa [G2] using G2.measure_reject_eq () c

/-- Type I error is exactly the nominal level. -/
example {c : ℝ} (hc : chiSqOneTail c = 1 / 20) :
    gaussianReal 0 2 {x | c < x ^ 2 / 2} = 1 / 20 := by
  simpa [G2] using G2.typeI_eq hc ()

/-- Without the correction the same test is strictly anti-conservative. -/
example : chiSqOneTail 1 < gaussianReal 0 2 {x | 1 < x ^ 2} := by
  simpa [G2] using G2.chiSqOneTail_lt_measure_reject_uncorrected (by simp [G2]) () one_pos

/-! ### Distributional calibration: breaks outside the model

A marker whose true null variance is not the common `λ = 2`. -/

/-- True variance `4 > λ = 2`: dividing by `2` leaves the test strictly anti-conservative. -/
example : chiSqOneTail 1 < gaussianReal 0 4 {x | 1 < x ^ 2 / 2} := by
  have h := chiSqOneTail_lt_measure_reject_of_lt (HasLaw.id (μ := gaussianReal 0 (4 : ℝ≥0)))
    (lam := 2) two_pos (by norm_num) one_pos
  simpa using h

/-- True variance `1 < λ = 2`: dividing by `2` makes the test strictly conservative. -/
example : gaussianReal 0 1 {x | 1 < x ^ 2 / 2} < chiSqOneTail 1 := by
  have h := measure_reject_lt_chiSqOneTail_of_gt one_ne_zero
    (HasLaw.id (μ := gaussianReal 0 (1 : ℝ≥0))) (lam := 2) (by norm_num) one_pos
  simpa using h

/-- The misspecified rejection probability is the `χ²₁` tail at a shifted threshold. -/
example : gaussianReal 0 4 {x | 1 < x ^ 2 / 2} = chiSqOneTail (1 / 2) := by
  have h := measure_reject_eq_chiSqOneTail (by norm_num)
    (HasLaw.id (μ := gaussianReal 0 (4 : ℝ≥0))) (k := 2) two_pos 1
  norm_num at h
  simpa using h

/-! ### Moment calibration in the LD-score model

A sample space of `8` equally likely points carrying the seven mean-zero, mutually orthogonal
rows of the Sylvester–Hadamard matrix `H₈`; scaled rows give effects and noise with exactly
the second moments the model requires. -/

/-- The uniform probability measure on `Fin 8`. -/
noncomputable def μ8 : Measure (Fin 8) := (8⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ8 :=
  ⟨by simpa [μ8] using ENNReal.inv_mul_cancel (by norm_num : (8 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

/-- Expectation under `μ8` is the average of the eight values. -/
theorem integral_μ8 (f : Fin 8 → ℝ) :
    ∫ ω, f ω ∂μ8 = (f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7) / 8 := by
  simp only [μ8, integral_smul_measure, integral_count, Fin.sum_univ_eight]
  norm_num
  ring

/-- Rows `1, …, 7` of the Sylvester–Hadamard matrix `H₈` (`H r c = (-1) ^ popcount (r ∧ c)`). -/
noncomputable def hrow : Fin 7 → Fin 8 → ℝ :=
  ![![1, -1, 1, -1, 1, -1, 1, -1],
    ![1, 1, -1, -1, 1, 1, -1, -1],
    ![1, -1, -1, 1, 1, -1, -1, 1],
    ![1, 1, 1, 1, -1, -1, -1, -1],
    ![1, -1, 1, -1, -1, 1, -1, 1],
    ![1, 1, -1, -1, -1, -1, 1, 1],
    ![1, -1, -1, 1, -1, 1, 1, -1]]

/-- No polygenic signal: `N = 4`, `M = 2`, `h² = 0`, unit-variance noise from rows `1–4`. -/
noncomputable def D0 : Model μ8 4 2 where
  h2 := 0
  beta := fun _ _ => 0
  eps := fun i => hrow ⟨i, by omega⟩
  memLp_beta := fun _ => MemLp.of_discrete
  memLp_eps := fun _ => MemLp.of_discrete
  integral_beta_mul := by intro k l; split_ifs <;> simp
  integral_eps_mul := by
    intro i i'
    fin_cases i <;> fin_cases i' <;> simp [integral_μ8, hrow] <;> norm_num
  integral_beta_mul_eps := by intro k i; simp

theorem D0_hβ : ∀ k, ∫ ω, D0.beta k ω ∂μ8 = 0 := fun _ => by simp [D0]

theorem D0_hε : ∀ i, ∫ ω, D0.eps i ω ∂μ8 = 0 := fun i => by
  fin_cases i <;> simp [D0, integral_μ8, hrow]

/-- Two orthogonal standardized markers. -/
def X0 : Matrix (Fin 4) (Fin 2) ℝ := !![1, 1; 1, -1; -1, 1; -1, -1]

theorem isStandardized_X0 : IsStandardized X0 := by
  intro k
  fin_cases k <;> simp [X0, Fin.sum_univ_four] <;> norm_num

/-- **Holds.** Stratification axis `c = (1, 0, 0, 0)`: both markers have `X_jᵀ c / N = ± 1/4`,
so the stratification term is common (`a = 1/16`), `λ_GC = 1 + 4/16 = 5/4`, and genomic
control calibrates both markers in mean. -/
example : lambdaGC D0 X0 1 ![1, 0, 0, 0] = 5 / 4 ∧
    ∀ j, (∫ ω, chiSqStrat D0 X0 1 ![1, 0, 0, 0] j ω ∂μ8) / lambdaGC D0 X0 1 ![1, 0, 0, 0] = 1 := by
  have h := integral_chiSqStrat_div_lambdaGC_of_null D0 X0 (by norm_num) (by norm_num)
    isStandardized_X0 D0_hβ D0_hε rfl 1 ![1, 0, 0, 0] (a := 1 / 16)
    (fun j => by fin_cases j <;> simp [X0, Fin.sum_univ_four] <;> norm_num)
  refine ⟨?_, h.2⟩
  rw [h.1]
  norm_num

/-- **Breaks.** Stratification axis `c = (1, 1, 0, 0)` lies along marker `0` and is orthogonal
to marker `1` (terms `1/4` and `0`): no single `λ` calibrates both markers. -/
example : ¬ ∃ lam : ℝ, (∫ ω, chiSqStrat D0 X0 1 ![1, 1, 0, 0] 0 ω ∂μ8) / lam = 1 ∧
    (∫ ω, chiSqStrat D0 X0 1 ![1, 1, 0, 0] 1 ω ∂μ8) / lam = 1 :=
  not_exists_lambda_calibrates_of_strat_ne D0 X0 (by norm_num) isStandardized_X0 D0_hβ D0_hε rfl
    1 ![1, 1, 0, 0] (j := 0) (k := 1) (by simp [X0, Fin.sum_univ_four])

/-- Polygenic signal: `N = 4`, `M = 3`, `h² = 3/4`; effects `(1/2) × rows 5–7` and noise
`(1/2) × rows 1–4`, so `𝔼[β²] = 1/4 = h² / M` and `𝔼[ε²] = 1/4 = 1 - h²`. -/
noncomputable def D1 : Model μ8 4 3 where
  h2 := 3 / 4
  beta := fun k ω => 1 / 2 * hrow ⟨k + 4, by omega⟩ ω
  eps := fun i ω => 1 / 2 * hrow ⟨i, by omega⟩ ω
  memLp_beta := fun _ => MemLp.of_discrete
  memLp_eps := fun _ => MemLp.of_discrete
  integral_beta_mul := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp [integral_μ8, hrow] <;> norm_num
  integral_eps_mul := by
    intro i i'
    fin_cases i <;> fin_cases i' <;> simp [integral_μ8, hrow] <;> norm_num
  integral_beta_mul_eps := by
    intro k i
    fin_cases k <;> fin_cases i <;> simp [integral_μ8, hrow]

theorem D1_hβ : ∀ k, ∫ ω, D1.beta k ω ∂μ8 = 0 := fun k => by
  fin_cases k <;> simp [D1, integral_μ8, hrow]

theorem D1_hε : ∀ i, ∫ ω, D1.eps i ω ∂μ8 = 0 := fun i => by
  fin_cases i <;> simp [D1, integral_μ8, hrow]

/-- Markers `0` and `2` are identical (LD score `2`); marker `1` is orthogonal to both (LD score
`1`); the mean LD score is `5/3`. -/
def X1 : Matrix (Fin 4) (Fin 3) ℝ := !![1, 1, 1; 1, -1, 1; -1, 1, -1; -1, -1, -1]

theorem isStandardized_X1 : IsStandardized X1 := by
  intro k
  fin_cases k <;> simp [X1, Fin.sum_univ_four] <;> norm_num

theorem ldScore_X1_one : ldScore X1 1 = 1 := by
  simp [ldScore, ldCorr, X1, Fin.sum_univ_three, Fin.sum_univ_four]
  norm_num

theorem meanLDScore_X1 : meanLDScore X1 = 5 / 3 := by
  simp [meanLDScore, ldScore, ldCorr, X1, Fin.sum_univ_three, Fin.sum_univ_four]
  norm_num

/-- **Breaks (polygenic signal).** Even with no stratification (`s = 0`, `a = 0`), genomic
control miscalibrates marker `1`, whose LD score `1` is not the mean `5/3`. -/
example : (∫ ω, chiSqStrat D1 X1 0 0 1 ω ∂μ8) / lambdaGC D1 X1 0 0 ≠ 1 := by
  rw [Ne, integral_chiSqStrat_div_lambdaGC_eq_one_iff D1 X1 (by norm_num) (by norm_num)
    isStandardized_X1 D1_hβ D1_hε (by norm_num [D1]) 0 0 (a := 0) (fun j => by simp),
    ldScore_X1_one, meanLDScore_X1]
  norm_num

/-- Marker `1` (LD score `1`, below the mean `5/3`) is over-corrected in mean, and marker `0`
(LD score `2`, above the mean) is under-corrected. -/
example : (∫ ω, chiSqStrat D1 X1 0 0 1 ω ∂μ8) / lambdaGC D1 X1 0 0 < 1 ∧
    1 < (∫ ω, chiSqStrat D1 X1 0 0 0 ω ∂μ8) / lambdaGC D1 X1 0 0 := by
  have hD1 : D1.h2 ≠ 0 := by norm_num [D1]
  refine ⟨integral_chiSqStrat_div_lambdaGC_lt_one_of_lt D1 X1 (by norm_num) (by norm_num)
    isStandardized_X1 D1_hβ D1_hε hD1 0 0 (a := 0) (fun j => by simp) ?_,
    one_lt_integral_chiSqStrat_div_lambdaGC_of_lt D1 X1 (by norm_num) (by norm_num)
    isStandardized_X1 D1_hβ D1_hε hD1 0 0 (a := 0) (fun j => by simp) ?_⟩
  · rw [ldScore_X1_one, meanLDScore_X1]
    norm_num
  · rw [meanLDScore_X1]
    simp [ldScore, ldCorr, X1, Fin.sum_univ_three, Fin.sum_univ_four]
    norm_num

#print axioms chiSqOneTail_lt_of_lt
#print axioms measure_reject_eq_chiSqOneTail
#print axioms CommonInflationModel.measure_reject_eq
#print axioms CommonInflationModel.typeI_eq
#print axioms CommonInflationModel.chiSqOneTail_lt_measure_reject_uncorrected
#print axioms chiSqOneTail_lt_measure_reject_of_lt
#print axioms measure_reject_lt_chiSqOneTail_of_gt
#print axioms integral_chiSqStrat_sub_lambdaGC
#print axioms integral_chiSqStrat_div_lambdaGC_of_null
#print axioms lambdaGC_pos
#print axioms integral_chiSqStrat_div_lambdaGC_eq_one_iff
#print axioms integral_chiSqStrat_div_lambdaGC_lt_one_of_lt
#print axioms one_lt_integral_chiSqStrat_div_lambdaGC_of_lt
#print axioms not_exists_lambda_calibrates_of_strat_ne

end MathlibExtTest.Biology.StatisticalGenetics.RareVariantInference.GenomicControl
