/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.StatisticalGenetics.RareVariantInference.BurdenSKATO
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Biology.StatisticalGenetics.RareVariantInference.BurdenSKATO`

Worked example: two individuals, an intercept, `V = I`, so `P = I - J/2`.

* `G₂`: two variants, both carried once by individual `0`, weights `a = (1, 1)`. Then
  `C = G a = (2, 0)`, the burden score is `y₀ - y₁`, `Cᵀ P C = 2`, `Q_B = (y₀ - y₁)²`,
  `Q_SKAT = (y₀ - y₁)² / 2`, `Q_ρ = (1 + ρ)(y₀ - y₁)² / 2`; Cauchy–Schwarz is an equality.
* `G₁ = I`: each individual carries one variant. Then `C = (1, 1)` is the intercept, `P C = 0`,
  and the burden test has a degenerate null law (`N(0, 0)`) although every individual carries a
  rare allele, while SKAT keeps `Q_SKAT = (y₀ - y₁)² / 2`.

Davies' formula itself (including the all-zero-weights boundary) is tested with its module,
`MathlibExt.Probability.Distributions.DaviesFormula`; here it is applied to SKAT-O. -/

open MeasureTheory ProbabilityTheory Matrix WithLp Filter Topology Set
open MathlibExt.Biology.StatisticalGenetics.BurdenSKAT
open MathlibExt.Biology.StatisticalGenetics.BurdenSKATO
open MathlibExt.Probability.Distributions.DaviesFormula
open MathlibExt.Probability.Statistics.GeneralizedLeastSquares
open scoped MatrixOrder

namespace MathlibExtTest.BurdenSKATO

/-! ### Smoke tests (API-00) -/

example : burdenQ (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = 0 := by
  simp [burdenQ, burdenScore_eq]

example : kernelQ (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 0 0 = 0 := by simp [kernelQ]

/-- `R₀ = I`. -/
example : (skatOCorr 0 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by simp [skatOCorr]

/-- `R₁ = 𝟙 𝟙ᵀ`. -/
example : (skatOCorr 1 : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.of fun _ _ => 1 := by
  simp [skatOCorr]

/-! ### Fixtures -/

/-- The intercept. -/
def X0 : Matrix (Fin 2) (Fin 1) ℝ := !![1; 1]

/-- The null projection `P = I - J/2`. -/
noncomputable def P0 : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, -1 / 2; -1 / 2, 1 / 2]

theorem gram_X0 : X0ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * X0 = !![2] := by
  ext i j
  fin_cases i; fin_cases j
  simp [X0, mul_apply, Fin.sum_univ_two]
  norm_num

theorem isUnit_X0 : IsUnit (X0ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * X0) := by
  rw [gram_X0, isUnit_iff_isUnit_det]
  simp

theorem projP_X0 : projP X0 1 = P0 := by
  have hinv : (!![2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![1 / 2] := by
    refine inv_eq_left_inv ?_
    ext i j
    fin_cases i; fin_cases j
    simp
  have hgls : glsMatrix X0 1 = !![1 / 2, 1 / 2] := by
    rw [glsMatrix, gram_X0, hinv, inv_one, Matrix.mul_one]
    ext i j
    fin_cases i; fin_cases j <;> simp [X0, vecMul, dotProduct]
  rw [projP, hgls, inv_one, Matrix.one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X0, P0] <;> norm_num

/-- Two variants, both carried once by individual `0`. -/
def G2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 0]

/-- Each individual carries one variant. -/
def G1 : Matrix (Fin 2) (Fin 2) ℝ := 1

/-- Unit weights. -/
def a1 : Fin 2 → ℝ := ![1, 1]

/-! ### Burden test on `G₂` -/

/-- The burden score is `y₀ - y₁`. -/
theorem burdenScore_G2 (y : Fin 2 → ℝ) : burdenScore X0 1 G2 a1 y = y 0 - y 1 := by
  rw [burdenScore_eq, projP_X0]
  simp [G2, a1, P0, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- `Q_B(3, 1) = 4`. -/
example : burdenQ X0 1 G2 a1 ![3, 1] = 4 := by
  rw [burdenQ, burdenScore_G2]; norm_num

/-- The null variance `Cᵀ P C = 2`. -/
theorem burdenVar_G2 : burdenVar X0 1 G2 a1 = 2 := by
  rw [burdenVar, projP_X0]
  simp [G2, a1, P0, mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

/-- The null law of the burden score is `N(0, 2)`. -/
example (α : Fin 1 → ℝ) :
    (multivariateGaussian (toLp 2 (X0 *ᵥ α)) 1).map
        (fun y => burdenScore X0 1 G2 a1 (ofLp y)) = gaussianReal 0 2 := by
  rw [map_burdenScore_null PosDef.one isUnit_X0 α, burdenVar_G2]
  congr 1
  norm_num

/-- The null law of the burden statistic is `2 χ²₁`, with mean `2`. -/
example (α : Fin 1 → ℝ) :
    (multivariateGaussian (toLp 2 (X0 *ᵥ α)) 1).map
        (fun y => burdenQ X0 1 G2 a1 (ofLp y)) = weightedChiSq (fun _ : Unit => (2 : ℝ)) := by
  rw [map_burdenQ_null PosDef.one isUnit_X0 α, burdenVar_G2]

example (α : Fin 1 → ℝ) :
    ∫ y, burdenQ X0 1 G2 a1 (ofLp y) ∂multivariateGaussian (toLp 2 (X0 *ᵥ α)) 1 = 2 := by
  rw [integral_burdenQ_null PosDef.one isUnit_X0 α, burdenVar_G2]

/-! ### SKAT and SKAT-O on `G₂` -/

/-- `Q_SKAT = (y₀ - y₁)² / 2` with weights `aⱼ² = 1`. -/
theorem skatQ_G2 (y : Fin 2 → ℝ) :
    skatQ X0 1 G2 (fun j => a1 j ^ 2) y = (y 0 - y 1) ^ 2 / 2 := by
  rw [skatQ_eq_sum_variantScore, variantScore, projP_X0]
  simp [G2, a1, P0, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- `Q_ρ = (1 + ρ)(y₀ - y₁)² / 2`. -/
theorem skatOQ_G2 (ρ : ℝ) (y : Fin 2 → ℝ) :
    skatOQ X0 1 G2 a1 ρ y = (1 + ρ) * (y 0 - y 1) ^ 2 / 2 := by
  rw [skatOQ, skatQ_G2, burdenQ, burdenScore_G2]
  ring

/-- Cauchy–Schwarz `Q_B ≤ m Q_SKAT` holds with equality here (`m = 2`). -/
example (y : Fin 2 → ℝ) :
    burdenQ X0 1 G2 a1 y = Fintype.card (Fin 2) * skatQ X0 1 G2 (fun j => a1 j ^ 2) y := by
  rw [burdenQ, burdenScore_G2, skatQ_G2]
  simp
  ring

/-- The kernel form agrees with the convex combination at `ρ = 1/2`, `y = (3, 1)`. -/
example : kernelQ X0 1 (skatOKernel G2 a1 (1 / 2)) ![3, 1] = 3 := by
  rw [← skatOQ_eq_kernelQ, skatOQ_G2]
  norm_num

/-- The burden kernel `C Cᵀ` with `C = (2, 0)`. -/
theorem burdenKernel_G2 : burdenKernel G2 a1 = !![4, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burdenKernel, G2, a1, vecMulVec_apply]; norm_num

/-- The null mixture matrix of the burden kernel: `P K_B P = [[1, -1], [-1, 1]]`. -/
theorem kernelMixtureMatrix_burden_G2 :
    kernelMixtureMatrix X0 1 (burdenKernel G2 a1) 1 = !![1, -1; -1, 1] := by
  rw [kernelMixtureMatrix, CFC.sqrt_one, Matrix.mul_one, projP_X0, burdenKernel_G2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P0, mul_apply, Fin.sum_univ_two] <;> norm_num

/-- At `ρ = 1` the SKAT-O kernel is the burden kernel. -/
theorem skatOKernel_one_G2 : skatOKernel G2 a1 1 = burdenKernel G2 a1 := by
  rw [skatOKernel_eq]; simp

/-- The SKAT-O null law on `G₂`. -/
example (α : Fin 1 → ℝ) (ρ : ℝ) :
    (multivariateGaussian (toLp 2 (X0 *ᵥ α)) 1).map (fun y => skatOQ X0 1 G2 a1 ρ (ofLp y)) =
      weightedChiSq (isHermitian_kernelMixtureMatrix (X := X0) (V := 1)
        (isHermitian_skatOKernel (G := G2) (a := a1) ρ) 1).eigenvalues :=
  map_skatOQ_multivariateGaussian isUnit_X0 ρ α 1

/-- Each SKAT-O p-value on `G₂` is valid. -/
example (α : Fin 1 → ℝ) (ρ : ℝ) :
    MathlibExt.Probability.Statistics.MultipleTesting.IsValidPValue
      (multivariateGaussian (toLp 2 (X0 *ᵥ α)) 1) fun y => skatOPValue X0 1 G2 a1 ρ (ofLp y) :=
  isValidPValue_skatOPValue isUnit_X0 α ρ

/-- At `ρ = 1` the null mixture has a nonzero weight (its matrix is nonzero), so Davies' integral
converges to the SKAT-O p-value at every phenotype. -/
example (y : Fin 2 → ℝ) : ∃ j, Tendsto (fun T => 1 / 2 + Real.pi⁻¹ * ∫ t in (0 : ℝ)..T,
    (Complex.exp (-(t * skatOQ X0 1 G2 a1 1 y) * Complex.I) *
      daviesCharFun (isHermitian_kernelMixtureMatrix (X := X0) (V := 1)
        (isHermitian_skatOKernel (G := G2) (a := a1) 1) 1).eigenvalues t).im / t) atTop
      (𝓝 (skatOPValue X0 1 G2 a1 1 y)) ∧
    (isHermitian_kernelMixtureMatrix (X := X0) (V := 1)
        (isHermitian_skatOKernel (G := G2) (a := a1) 1) 1).eigenvalues j ≠ 0 := by
  set hA := isHermitian_kernelMixtureMatrix (X := X0) (V := 1)
    (isHermitian_skatOKernel (G := G2) (a := a1) 1) 1
  have hne : hA.eigenvalues ≠ 0 := by
    rw [Ne, hA.eigenvalues_eq_zero_iff, skatOKernel_one_G2, kernelMixtureMatrix_burden_G2]
    intro h
    have := congrFun (congrFun h 0) 0
    simp at this
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  exact ⟨j, tendsto_davies_skatOPValue 1 hj y, hj⟩

/-! ### Boundary: burden collinear with the covariates (`G₁ = I`) -/

/-- `Cᵀ P C = 0`: the collapsed genotype `(1, 1)` is the intercept. -/
theorem burdenVar_G1 : burdenVar X0 1 G1 a1 = 0 := by
  rw [burdenVar, projP_X0]
  simp [G1, a1, P0, mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

/-- The burden null law is the point mass at `0`, although every individual carries a rare
allele. -/
example (α : Fin 1 → ℝ) :
    (multivariateGaussian (toLp 2 (X0 *ᵥ α)) 1).map
        (fun y => burdenScore X0 1 G1 a1 (ofLp y)) = Measure.dirac 0 := by
  rw [map_burdenScore_null PosDef.one isUnit_X0 α, burdenVar_G1, Real.toNNReal_zero,
    gaussianReal_zero_var]

/-- SKAT still sees the data: `Q_SKAT = (y₀ - y₁)² / 2`. -/
example (y : Fin 2 → ℝ) : skatQ X0 1 G1 (fun j => a1 j ^ 2) y = (y 0 - y 1) ^ 2 / 2 := by
  rw [skatQ_eq_sum_variantScore, variantScore, projP_X0]
  simp [G1, a1, P0, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-! ### Boundary: zero minor-allele count -/

/-- No carriers: the burden null law is the point mass at `0`. -/
example (α : Fin 1 → ℝ) :
    (multivariateGaussian (toLp 2 (X0 *ᵥ α)) 1).map
        (fun y => burdenScore X0 1 (0 : Matrix (Fin 2) (Fin 2) ℝ) a1 (ofLp y)) =
      Measure.dirac 0 :=
  map_burdenScore_null_of_collapse_eq_zero PosDef.one isUnit_X0 α (by simp)

/-- Variant `1` has no carriers in `!![1, 0; 0, 0]`, so its weight does not change the burden
score. -/
example (y : Fin 2 → ℝ) (c : ℝ) :
    burdenScore X0 1 !![1, 0; 0, 0] (Function.update a1 1 c) y =
      burdenScore X0 1 !![1, 0; 0, 0] a1 y :=
  burdenScore_update_of_col (fun i => by fin_cases i <;> simp) c y

/-! ### SKAT-O min-p validity -/

/-- The Bonferroni bound on the grid `{0, 1/2, 1}`. -/
example (α : Fin 1 → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    multivariateGaussian (toLp 2 (X0 *ᵥ α)) 1
        {y | skatOMinP X0 1 G2 a1 {0, 1 / 2, 1} (by simp) (ofLp y) ≤ t} ≤
      ({0, 1 / 2, 1} : Finset ℝ).card * ENNReal.ofReal t :=
  measure_skatOMinP_le isUnit_X0 α _ _ ht

end MathlibExtTest.BurdenSKATO
