/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.StatisticalGenetics.RareVariantInference.BurdenSKAT
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Biology.StatisticalGenetics.RareVariantInference.BurdenSKAT`

The worked example has two unrelated founders, so the pedigree relationship matrix is `I`.
It uses an intercept covariate, `σ_g² = σ_e² = 1/2` (hence `Σ₀ = I`), and one variant carried
once, by individual `0`. Then `P = I - J/2`, `Q(y) = (y₀ - y₁)² / 4`, the mixture matrix is
`P K P = [[1/4, -1/4], [-1/4, 1/4]]`, and the null law is `½ χ²₁ + 0 · χ²₁`. The null law is
computed in an explicit orthonormal eigenbasis, `(1, -1)/√2` and `(1, 1)/√2`. -/

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder
open MathlibExt.Biology.StatisticalGenetics.BurdenSKAT
open MathlibExt.Biology.StatisticalGenetics.Kinship
open MathlibExt.Probability.Statistics.GeneralizedLeastSquares

namespace MathlibExtTest.BurdenSKAT

/-! ### Smoke test (API-00) -/

/-- The statistic, its kernel and the mixture law typecheck on a trivial instance. -/
example : skatQ (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = 0 := by
  simp

example : weightedChiSq (0 : Fin 3 → ℝ) = Measure.dirac 0 := weightedChiSq_zero

/-! ### Fixtures -/

/-- Two unrelated founders. -/
def twoFounders : Pedigree 2 where
  parents := ![none, none]
  parents_lt := by
    intro i g h k
    fin_cases i <;> simp at h

/-- The relationship matrix of two unrelated non-inbred founders is the identity. -/
theorem pedigreeRelationship_twoFounders : pedigreeRelationship twoFounders = 1 := by
  ext i j
  have h0 : twoFounders.parents 0 = none := rfl
  have h1 : twoFounders.parents 1 = none := rfl
  fin_cases i <;> fin_cases j <;>
    simp [pedigreeRelationship, twoFounders.kinship_self_of_parents_eq_none h0,
      twoFounders.kinship_self_of_parents_eq_none h1,
      twoFounders.kinship_of_lt_of_parents_eq_none (show (0 : Fin 2) < 1 by decide) h1,
      twoFounders.kinship_of_gt_of_parents_eq_none (show (0 : Fin 2) < 1 by decide) h1]

/-- With `σ_g² = σ_e² = 1/2` the famSKAT null covariance is `I`. -/
theorem nullCov_twoFounders :
    nullCov (pedigreeRelationship twoFounders) (1 / 2) (1 / 2) = 1 := by
  rw [nullCov, pedigreeRelationship_twoFounders, ← add_smul]
  norm_num

/-- The intercept. -/
def X0 : Matrix (Fin 2) (Fin 1) ℝ := !![1; 1]

/-- One variant, carried once (heterozygous) by individual `0`. -/
def G0 : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The null projection `P = I - J/2`. -/
noncomputable def P0 : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, -1 / 2; -1 / 2, 1 / 2]

/-- The null mixture matrix `P K P`. -/
noncomputable def A0 : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 4, -1 / 4; -1 / 4, 1 / 4]

theorem gram_X0 : X0ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * X0 = !![2] := by
  ext i j
  fin_cases i; fin_cases j
  simp [X0, mul_apply, Fin.sum_univ_two]
  norm_num

theorem isUnit_X0 : IsUnit (X0ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * X0) := by
  rw [gram_X0, isUnit_iff_isUnit_det]
  simp

theorem glsMatrix_X0 : glsMatrix X0 1 = !![1 / 2, 1 / 2] := by
  have hinv : (!![2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![1 / 2] := by
    refine inv_eq_left_inv ?_
    ext i j
    fin_cases i; fin_cases j
    simp
  rw [glsMatrix, gram_X0, hinv, inv_one, Matrix.mul_one]
  ext i j
  fin_cases i; fin_cases j <;> simp [X0, vecMul, dotProduct]

theorem projP_X0 : projP X0 1 = P0 := by
  rw [projP, glsMatrix_X0, inv_one, Matrix.one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X0, P0] <;> norm_num

/-! ### The worked example: statistic and null law -/

/-- The weight vector of the single variant. -/
def w0 : Fin 1 → ℝ := ![1]

/-- `Q(y) = (y₀ - y₁)² / 4`. -/
theorem skatQ_example (y : Fin 2 → ℝ) : skatQ X0 1 G0 w0 y = (y 0 - y 1) ^ 2 / 4 := by
  rw [skatQ_eq_sum_variantScore, variantScore, projP_X0]
  simp [w0, G0, P0, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The phenotype `y = (3, 1)` gives `Q = 1`. -/
example : skatQ X0 1 G0 w0 ![3, 1] = 1 := by
  rw [skatQ_example]; norm_num

/-- The same value through the single-variant score `S = (y₀ - y₁)/2 = 1`. -/
example : variantScore X0 1 G0 ![3, 1] 0 = 1 := by
  rw [variantScore, projP_X0]
  simp [G0, P0, mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

theorem skatKernel_example : skatKernel G0 w0 = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skatKernel, G0, w0, mul_apply, vecMul_diagonal]

theorem skatMixtureMatrix_example : skatMixtureMatrix X0 1 G0 w0 1 = A0 := by
  rw [skatMixtureMatrix, CFC.sqrt_one, Matrix.mul_one, projP_X0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skatKernel_example, P0, A0, mul_apply, Fin.sum_univ_two] <;> norm_num

/-- `1/√2`. -/
noncomputable def c : ℝ := √(1 / 2)

theorem c_mul_c : c * c = 1 / 2 := Real.mul_self_sqrt (by norm_num)

theorem c_sq : c ^ 2 = 1 / 2 := by rw [sq, c_mul_c]

/-- The eigenvectors `(1, -1)/√2` (eigenvalue `1/2`) and `(1, 1)/√2` (eigenvalue `0`). -/
noncomputable def eigvec : Fin 2 → EuclideanSpace ℝ (Fin 2) := ![toLp 2 ![c, -c], toLp 2 ![c, c]]

theorem orthonormal_eigvec : Orthonormal ℝ eigvec := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [eigvec, EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_two, c_mul_c,
      EuclideanSpace.norm_eq, sq_abs, c_sq] <;>
    norm_num

/-- The explicit orthonormal eigenbasis of `A0`. -/
noncomputable def eigBasis : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  OrthonormalBasis.mk orthonormal_eigvec
    (orthonormal_eigvec.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge

theorem mulVec_eigBasis (j : Fin 2) :
    A0 *ᵥ ⇑(eigBasis j) = (![1 / 2, 0] : Fin 2 → ℝ) j • ⇑(eigBasis j) := by
  simp only [eigBasis, OrthonormalBasis.coe_mk]
  fin_cases j <;> ext i <;> fin_cases i <;>
    simp [eigvec, A0, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- **The null law in the worked example**: for every intercept `α`, under
`y ~ N(α 𝟙, Σ₀)` with the two-founder kinship, `Q ~ ½ χ²₁ + 0 · χ²₁`. -/
theorem null_law_example (α : Fin 1 → ℝ) :
    (multivariateGaussian (toLp 2 (X0 *ᵥ α))
        (nullCov (pedigreeRelationship twoFounders) (1 / 2) (1 / 2))).map
      (fun y => skatQ X0 (nullCov (pedigreeRelationship twoFounders) (1 / 2) (1 / 2)) G0 w0
        (ofLp y)) = weightedChiSq ![1 / 2, 0] := by
  simp only [nullCov_twoFounders]
  have hA := isHermitian_skatMixtureMatrix (X := X0) (V := 1) (G := G0) (w := w0) 1
  rw [map_skatQ_multivariateGaussian isUnit_X0,
    ← stdGaussian_map_inner_eq_weightedChiSq _ hA.eigenvectorBasis _ hA.mulVec_eigenvectorBasis,
    skatMixtureMatrix_example]
  exact stdGaussian_map_inner_eq_weightedChiSq A0 eigBasis _ mulVec_eigBasis

/-- The null mean in the example is `tr(K P) = 1/2`, the total mixture weight. -/
theorem null_mean_example (α : Fin 1 → ℝ) :
    ∫ y, skatQ X0 1 G0 w0 (ofLp y) ∂multivariateGaussian (toLp 2 (X0 *ᵥ α)) 1 = 1 / 2 := by
  rw [integral_skatQ_null PosDef.one isUnit_X0, projP_X0]
  simp [trace, skatKernel_example, P0, Fin.sum_univ_two]

example : ∫ x, x ∂weightedChiSq (![1 / 2, 0] : Fin 2 → ℝ) = 1 / 2 := by
  rw [integral_weightedChiSq]; simp

/-! ### Kinship -/

example : (pedigreeRelationship twoFounders).PosSemidef := posSemidef_pedigreeRelationship _

example : (nullCov (pedigreeRelationship twoFounders) (1 / 2) (1 / 2)).PosDef :=
  posDef_nullCov_pedigreeRelationship _ (by norm_num) (by norm_num)

/-! ### Boundary case: rare alleles -/

example : betaWeight 0 = 625 := betaWeight_zero

/-- A variant at MAF `1/100` gets at least the weight of one at MAF `1/4`. -/
example : betaWeight (1 / 4) ≤ betaWeight (1 / 100) :=
  betaWeight_antitoneOn ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)

/-- The weight scales the statistic: `Q = c (y₀ - y₁)² / 4` for weight `c`. -/
example (c : ℝ) (y : Fin 2 → ℝ) : skatQ X0 1 G0 ![c] y = c * ((y 0 - y 1) ^ 2 / 4) := by
  rw [skatQ_eq_sum_variantScore, variantScore, projP_X0]
  simp [G0, P0, mulVec, dotProduct, Fin.sum_univ_two, -mul_eq_mul_left_iff]
  ring

/-- With the Beta(1, 25) weight of the singleton (MAF `1/4` among four alleles) the null mean is
`w · gᵀ P g = w · P₀₀ = w / 2`. -/
example (α : Fin 1 → ℝ) :
    ∫ y, skatQ X0 1 G0 ![betaWeight (1 / 4)] (ofLp y) ∂multivariateGaussian (toLp 2 (X0 *ᵥ α)) 1 =
      betaWeight (1 / 4) / 2 := by
  rw [integral_skatQ_null_eq_sum PosDef.one isUnit_X0, projP_X0]
  simp [G0, P0, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-! ### Boundary case: zero minor-allele count -/

/-- Two variants; the second has no carriers. -/
def G1 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

theorem G1_col_one (i : Fin 2) : G1 i 1 = 0 := by fin_cases i <;> rfl

example (y : Fin 2 → ℝ) : variantScore X0 1 G1 y 1 = 0 :=
  variantScore_eq_zero_of_col G1_col_one y

/-- The weight of the carrier-free variant does not affect `Q`. -/
example (w : Fin 2 → ℝ) (c : ℝ) (y : Fin 2 → ℝ) :
    skatQ X0 1 G1 (Function.update w 1 c) y = skatQ X0 1 G1 w y :=
  skatQ_update_of_col G1_col_one c y

/-- No carriers at all: the law of `Q` is the point mass at `0`. -/
example (α : Fin 1 → ℝ) :
    (multivariateGaussian (toLp 2 (X0 *ᵥ α)) 1).map
      (fun y => skatQ X0 1 (0 : Matrix (Fin 2) (Fin 1) ℝ) w0 (ofLp y)) = Measure.dirac 0 :=
  map_skatQ_zero_genotype _ _

example : (isHermitian_skatMixtureMatrix (X := X0) (V := 1) (G := (0 : Matrix (Fin 2) (Fin 1) ℝ))
    (w := w0) 1).eigenvalues = 0 :=
  eigenvalues_skatMixtureMatrix_zero_genotype 1

/-! ### Boundary case: singular kinship -/

/-- A singular relationship matrix (a duplicated individual, or monozygotic twins). -/
def Φs : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]

theorem posSemidef_Φs : Φs.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · have h : star x ⬝ᵥ Φs *ᵥ x = (x 0 + x 1) ^ 2 := by
      simp [Φs, mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [h]
    positivity

theorem Φs_mulVec : Φs *ᵥ ![1, -1] = 0 := by
  ext i
  fin_cases i <;> simp [Φs, mulVec, dotProduct, Fin.sum_univ_two]

/-- With noise the singular kinship still gives a positive definite `Σ₀`. -/
example : (nullCov Φs 1 1).PosDef := posDef_nullCov posSemidef_Φs zero_le_one one_pos

theorem det_nullCov_Φs : (nullCov Φs 1 0).det = 0 :=
  det_nullCov_zero (v := ![1, -1]) (fun h => by simpa using congrFun h 0) Φs_mulVec

/-- Without noise the GLS-based statistic collapses to `0`. -/
example (y : Fin 2 → ℝ) : skatQ X0 (nullCov Φs 1 0) G0 w0 y = 0 :=
  skatQ_of_det_eq_zero det_nullCov_Φs y

/-- Without noise the phenotypes of the two individuals differ by a constant almost surely. -/
example (μ : EuclideanSpace ℝ (Fin 2)) :
    ∀ᵐ y ∂multivariateGaussian μ (nullCov Φs 1 0), y 0 - y 1 = μ 0 - μ 1 := by
  have hS : (nullCov Φs 1 0).PosSemidef := by simpa [nullCov] using posSemidef_Φs
  filter_upwards [ae_dotProduct_sub_eq_zero hS (nullCov_zero_mulVec Φs_mulVec) μ] with y hy
  simp [dotProduct, Fin.sum_univ_two] at hy
  linarith

/-! ### Boundary case: the variance component at `τ = 0` -/

theorem w0_nonneg : 0 ≤ w0 := fun j => by fin_cases j; simp [w0]

example (y : Fin 2 → ℝ) : 0 ≤ skatQ X0 1 G0 w0 y := skatQ_nonneg w0_nonneg y

example : altCov 1 G0 w0 0 = 1 := altCov_zero 1

/-- Under the null the law of `Q` has no mass below `0`. -/
example (α : Fin 1 → ℝ) :
    (multivariateGaussian (toLp 2 (X0 *ᵥ α)) 1).map (fun y => skatQ X0 1 G0 w0 (ofLp y))
      (Set.Iio 0) = 0 :=
  map_skatQ_null_Iio isUnit_X0 w0_nonneg α

/-- Along the alternative, `𝔼_τ Q = 1/2 + τ/4`, increasing away from the boundary `τ = 0`. -/
theorem alt_mean_example {τ : ℝ} (hτ : 0 ≤ τ) (α : Fin 1 → ℝ) :
    ∫ y, skatQ X0 1 G0 w0 (ofLp y) ∂multivariateGaussian (toLp 2 (X0 *ᵥ α)) (altCov 1 G0 w0 τ) =
      1 / 2 + τ / 4 := by
  rw [integral_skatQ_altCov PosDef.one isUnit_X0 w0_nonneg hτ, projP_X0, skatKernel_example]
  simp [trace, P0, vecMul, dotProduct, Fin.sum_univ_two]
  ring

example {τ : ℝ} (hτ : 0 ≤ τ) (α : Fin 1 → ℝ) :
    ∫ y, skatQ X0 1 G0 w0 (ofLp y) ∂multivariateGaussian (toLp 2 (X0 *ᵥ α)) 1 ≤
      ∫ y, skatQ X0 1 G0 w0 (ofLp y) ∂multivariateGaussian (toLp 2 (X0 *ᵥ α))
        (altCov 1 G0 w0 τ) :=
  integral_skatQ_null_le_altCov PosDef.one isUnit_X0 w0_nonneg hτ α

/-! ### Axiom audit -/

#print axioms map_skatQ_multivariateGaussian
#print axioms integral_skatQ_altCov
#print axioms posSemidef_two_kinship
#print axioms null_law_example

end MathlibExtTest.BurdenSKAT
