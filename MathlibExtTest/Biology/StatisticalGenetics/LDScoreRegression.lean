/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScoreRegression

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
  MathlibExt.Biology.StatisticalGenetics.LDScoreRegression
  MathlibExt.Probability.FiniteProbability
open scoped ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.LDScoreRegression

/-! ### Least squares on concrete data, computed from the definitions -/

/-- LD scores `(2, 2, 1)` are not all equal: `S_ℓℓ = 2/3`. -/
example : sxy (![2, 2, 1] : Fin 3 → ℝ) ![2, 2, 1] = 2 / 3 := by
  simp [sxy, sampleMean_eq_sum_div, Fin.sum_univ_three]
  norm_num

/-- `ĥ²` from the definition: statistics `(5/2, 5/2, 7/4)` on LD scores `(2, 2, 1)` with
`N = 4`, `M = 3` have slope `3/4`, so `ĥ² = (3/4) · 3 / 4 = 9/16`. -/
example : olsH2Hat 4 3 ![2, 2, 1] ![5 / 2, 5 / 2, 7 / 4] = 9 / 16 := by
  simp [olsH2Hat, olsSlope, sxy, sampleMean_eq_sum_div, Fin.sum_univ_three]
  norm_num

/-- The same value through `olsH2Hat_affine`: the statistics are `1 + (4 · (9/16) / 3) ℓ`. -/
example : olsH2Hat 4 3 ![2, 2, 1] (fun j => 1 + ((4 : ℕ) : ℝ) * (9 / 16) / ((3 : ℕ) : ℝ) *
    (![2, 2, 1] : Fin 3 → ℝ) j) = 9 / 16 := by
  have hℓ : sxy (![2, 2, 1] : Fin 3 → ℝ) ![2, 2, 1] ≠ 0 := by
    simp [sxy, sampleMean_eq_sum_div, Fin.sum_univ_three]
    norm_num
  exact olsH2Hat_affine (by norm_num) (by norm_num) hℓ _ _

/-- The intercept from the definition is `1` for the same data. -/
example : olsIntercept (![2, 2, 1] : Fin 3 → ℝ) ![5 / 2, 5 / 2, 7 / 4] = 1 := by
  simp [olsIntercept, olsSlope, sxy, sampleMean_eq_sum_div, Fin.sum_univ_three]
  norm_num

/-- Boundary: equal LD scores leave the slope unidentified, and `ĥ²` is the junk value `0`
whatever the statistics. -/
example : olsH2Hat 4 3 ![1, 1, 1] ![1, 5, 9] = 0 := by
  simp [olsH2Hat, olsSlope, sxy, sampleMean_eq_sum_div, Fin.sum_univ_three]
  norm_num

/-- Boundary: `N = 0` gives `ĥ² = 0` by `x / 0 = 0`. -/
example (ℓ χ : Fin 3 → ℝ) : olsH2Hat 0 3 ℓ χ = 0 := by simp [olsH2Hat]

/-! ### A witness model with three markers

`N = 4` individuals, `M = 3` markers, `h² = 3/4`, on `Fin 8` with the uniform probability
measure. The seven non-constant Walsh functions `w₁, …, w₇` (rows of the Sylvester-Hadamard
matrix of order 8) are mean-zero, orthogonal, and have second moment `1`. The effects are
`β k = w_{k+1} / 2` (second moment `1/4 = h² / M`) and the noise terms are
`ε i = w_{i+4} / 2` (second moment `1/4 = 1 - h²`). -/

/-- The uniform probability measure on `Fin 8`. -/
noncomputable def μ8 : Measure (Fin 8) := (8⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ8 :=
  ⟨by simpa [μ8] using ENNReal.inv_mul_cancel (by norm_num : (8 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

theorem integral_μ8 (f : Fin 8 → ℝ) :
    ∫ ω, f ω ∂μ8 = (f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7) / 8 := by
  simp only [μ8, integral_smul_measure, integral_count, Fin.sum_univ_eight]
  norm_num
  ring

/-- The non-constant Walsh functions on `Fin 8`. -/
def walsh : Fin 7 → Fin 8 → ℝ :=
  ![![1, -1, 1, -1, 1, -1, 1, -1], ![1, 1, -1, -1, 1, 1, -1, -1],
    ![1, -1, -1, 1, 1, -1, -1, 1], ![1, 1, 1, 1, -1, -1, -1, -1],
    ![1, -1, 1, -1, -1, 1, -1, 1], ![1, 1, -1, -1, -1, -1, 1, 1],
    ![1, -1, -1, 1, -1, 1, 1, -1]]

/-- The witness model. -/
noncomputable def D : Model μ8 4 3 where
  h2 := 3 / 4
  beta := fun k ω => walsh (Fin.castLE (by norm_num) k) ω / 2
  eps := fun i ω => walsh (Fin.natAdd 3 i) ω / 2
  memLp_beta := fun _ => MemLp.of_discrete
  memLp_eps := fun _ => MemLp.of_discrete
  integral_beta_mul := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp [integral_μ8, walsh] <;> norm_num
  integral_eps_mul := by
    intro i i'
    fin_cases i <;> fin_cases i' <;> simp [integral_μ8, walsh] <;> norm_num
  integral_beta_mul_eps := by
    intro k i
    fin_cases k <;> fin_cases i <;> simp [integral_μ8, walsh] <;> norm_num

theorem hβ : ∀ k, ∫ ω, D.beta k ω ∂μ8 = 0 := fun k => by
  fin_cases k <;> simp [D, integral_μ8, walsh] <;> norm_num

theorem hε : ∀ i, ∫ ω, D.eps i ω ∂μ8 = 0 := fun i => by
  fin_cases i <;> simp [D, integral_μ8, walsh] <;> norm_num

/-- Three standardized markers: the first two identical, the third orthogonal to them. -/
def X : Matrix (Fin 4) (Fin 3) ℝ := !![1, 1, 1; 1, 1, -1; -1, -1, 1; -1, -1, -1]

theorem isStandardized_X : IsStandardized X := by
  intro k
  fin_cases k <;> simp [X, Fin.sum_univ_four] <;> norm_num

/-- The LD scores are `(2, 2, 1)`, computed from the definition. -/
theorem ldScore_X : ldScore X = ![2, 2, 1] := by
  funext j
  fin_cases j <;> simp [ldScore, ldCorr, X, Fin.sum_univ_four, Fin.sum_univ_three] <;> norm_num

/-- Non-vacuity of the identification hypothesis: these LD scores are not all equal. -/
theorem sxy_ldScore_X : sxy (ldScore X) (ldScore X) ≠ 0 := by
  rw [ldScore_X]
  simp [sxy, sampleMean_eq_sum_div, Fin.sum_univ_three]
  norm_num

/-- Stratification along `c = (1, 0, 0, 0)` with `s = 1`: every marker has `X_jᵀ c / N = 1/4`,
so the confounding term is common, `a = 1/16`. -/
theorem ha : ∀ j, (1 : ℝ) ^ 2 * ((∑ i, X i j * (![1, 0, 0, 0] : Fin 4 → ℝ) i) /
    ((4 : ℕ) : ℝ)) ^ 2 = 1 / 16 := by
  intro j
  fin_cases j <;> simp [X, Fin.sum_univ_four] <;> norm_num

/-- The exact regression identity for marker `2` (`ℓ = 1`):
`𝔼[χ²] = 1 + 4 (3/4) / 3 + 4 / 16 - 3/4 = 3/2`. -/
example : ∫ ω, chiSqStrat D X 1 ![1, 0, 0, 0] 2 ω ∂μ8 = 3 / 2 := by
  rw [integral_chiSqStrat_eq D X (by norm_num) isStandardized_X hβ hε 1 _ ha, ldScore_X]
  simp [D]
  norm_num

/-- The same value by direct computation of the expectation, not through the identity. -/
example : ∫ ω, chiSqStrat D X 1 ![1, 0, 0, 0] 2 ω ∂μ8 = 3 / 2 := by
  simp [integral_μ8, chiSqStrat, betaHatStrat, phenoStrat, Model.pheno, D, X, walsh,
    Fin.sum_univ_four, Fin.sum_univ_three]
  norm_num

/-- With `h² = 3/4 ≠ 0` the paper's form `1 + N h² ℓ / M + N a` is not exact. -/
example : ∫ ω, chiSqStrat D X 1 ![1, 0, 0, 0] 2 ω ∂μ8 ≠
    1 + ((4 : ℕ) : ℝ) * D.h2 * ldScore X 2 / ((3 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) * (1 / 16) := by
  rw [Ne, integral_chiSqStrat_eq_paper_iff D X (by norm_num) isStandardized_X hβ hε 1 _ ha]
  simp [D]

/-- Population consistency: `ĥ²` of the expected statistics is `h² = 3/4`. -/
example : olsH2Hat 4 3 (ldScore X) (fun j => ∫ ω, chiSqStrat D X 1 ![1, 0, 0, 0] j ω ∂μ8) =
    3 / 4 :=
  olsH2Hat_integral_chiSqStrat D X (by norm_num) (by norm_num) isStandardized_X sxy_ldScore_X hβ hε
    1 _ ha

/-- Unbiasedness: `𝔼[ĥ²] = h² = 3/4` despite the confounding term. -/
example : ∫ ω, olsH2Hat 4 3 (ldScore X) (fun j => chiSqStrat D X 1 ![1, 0, 0, 0] j ω) ∂μ8 =
    3 / 4 :=
  integral_olsH2Hat_chiSqStrat D X (by norm_num) (by norm_num) isStandardized_X sxy_ldScore_X hβ
    hε 1 _ ha

/-- The intercept is unbiased for `1 - h² + N a = 1 - 3/4 + 4/16 = 1/2`. -/
example : ∫ ω, olsIntercept (ldScore X) (fun j => chiSqStrat D X 1 ![1, 0, 0, 0] j ω) ∂μ8 =
    1 / 2 := by
  rw [integral_olsIntercept_chiSqStrat D X (by norm_num) isStandardized_X sxy_ldScore_X hβ hε 1
    _ ha]
  simp [D]
  norm_num

/-- `ĥ²` is genuinely random in the witness model: it differs between outcomes `0` and `1`
(computed from the definitions), so unbiasedness is not a deterministic identity. -/
example : olsH2Hat 4 3 (ldScore X) (fun j => chiSqStrat D X 0 0 j 0) ≠
    olsH2Hat 4 3 (ldScore X) (fun j => chiSqStrat D X 0 0 j 1) := by
  rw [ldScore_X]
  simp [olsH2Hat, olsSlope, sxy, sampleMean_eq_sum_div, chiSqStrat, betaHatStrat, phenoStrat,
    Model.pheno, D, X, walsh, Fin.sum_univ_four, Fin.sum_univ_three]
  norm_num

#print axioms integral_chiSqStrat_eq
#print axioms integral_olsH2Hat_chiSqStrat
#print axioms integral_olsIntercept_chiSqStrat
#print axioms tendstoInMeasure_olsH2Hat

end MathlibExtTest.Biology.StatisticalGenetics.LDScoreRegression
