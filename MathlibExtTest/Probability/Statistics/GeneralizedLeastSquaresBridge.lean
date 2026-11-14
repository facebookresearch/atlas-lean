/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GeneralizedLeastSquaresBridge
public import MathlibExt.Probability.FiniteProbability
public import MathlibExt.Biology.StatisticalGenetics.MixedModel
public import MathlibExt.Probability.Statistics.GeneralizedLeastSquares
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # Tests for `GeneralizedLeastSquaresBridge`

Finite two-observation examples: a design satisfying every hypothesis, with
`V = phenCov Z G R` entrywise; violated-assumption counterexamples (singular
`V`, rank-deficient `X`); and the BLUP-versus-GLS contrast
(`L * X = 0` against `B * X = 1`).
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.GeneralizedLeastSquaresBridge
open MathlibExt.Probability.Statistics.GeneralizedLeastSquares
open MathlibExt.Probability.FiniteProbability
open MathlibExt.Biology.StatisticalGenetics.MixedModel

namespace MathlibExtTest.GLSBridge

/-- Two observations of one mean. -/
abbrev tX : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun _ _ => 1

/-- Diagonal noise covariance `diag(1, 2)`. -/
abbrev tV : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 2]

/-- Random-effect loadings: only the first observation carries `u`. -/
abbrev tZ : Matrix (Fin 2) (Fin 1) ℝ :=
  Matrix.of fun i _ => if i = 0 then 1 else 0

/-- Random-effect covariance `(1 / 2) • 1`. -/
noncomputable abbrev tG : Matrix (Fin 1) (Fin 1) ℝ := (1 / 2 : ℝ) • 1

/-- Residual covariance `diag(1 / 2, 2)`. -/
noncomputable abbrev tR : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1 / 2, 2]

/-- Singular covariance: the all-ones matrix. -/
abbrev sV : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun _ _ => 1

private theorem hV : tV.PosDef :=
  Matrix.PosDef.diagonal (by intro i; fin_cases i <;> norm_num)

private theorem hVinv : tV⁻¹ = Matrix.diagonal ![1, 1 / 2] :=
  Matrix.inv_eq_left_inv (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp)

private theorem hX : IsUnit (tXᵀ * tV⁻¹ * tX) := by
  rw [Matrix.isUnit_iff_isUnit_det, hVinv]
  simp [Matrix.det_unique, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

private theorem hgram : IsUnit (tXᵀ * tX) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [Matrix.det_unique, Matrix.mul_apply]

private theorem hrank : LinearIndependent ℝ tX.col :=
  (isUnit_transpose_mul_self_iff tX).mp hgram

private theorem hG : tG.PosDef :=
  Matrix.PosDef.one.smul (by norm_num)

private theorem hR : tR.PosDef :=
  Matrix.PosDef.diagonal (by intro i; fin_cases i <;> norm_num)

private theorem hphen : phenCov tZ tG tR = tV := by
  unfold phenCov
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tZ, tG, tR, tV, Matrix.add_apply, Matrix.mul_apply] ;
    norm_num [Fin.mk_zero, Fin.mk_one]

private theorem hXm : IsUnit (tXᵀ * (phenCov tZ tG tR)⁻¹ * tX) := by
  rw [hphen]
  exact hX

/-- The finite example satisfies every hypothesis at once. -/
theorem bridge_finite_assumptions :
    tG.PosDef ∧ tR.PosDef ∧ tV.PosDef ∧ IsUnit (tXᵀ * tV⁻¹ * tX)
      ∧ LinearIndependent ℝ tX.col :=
  ⟨hG, hR, hV, hX, hrank⟩

/-- The marginal covariance is `phenCov Z G R` entrywise. -/
theorem bridge_phenCov_eq : phenCov tZ tG tR = tV :=
  hphen

/-- The GLS Gram value in the example is `3 / 2`. -/
theorem bridge_gram_value : (tXᵀ * tV⁻¹ * tX) 0 0 = 3 / 2 := by
  rw [hVinv]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

/-- GLS covariance identity in the example. -/
theorem bridge_gls_covariance :
    glsMatrix tX tV * tV * (glsMatrix tX tV)ᵀ = (tXᵀ * tV⁻¹ * tX)⁻¹ :=
  glsMatrix_mul_mul_transpose hV hX

private theorem sVdet : sV.det = 0 := by
  simp only [sV, Matrix.det_fin_two, Matrix.of_apply]
  norm_num

/-- Violated assumption: the all-ones covariance is not positive definite. -/
theorem bridge_singularV_not_posDef : ¬ sV.PosDef := by
  intro h
  have hpos := h.det_pos
  rw [sVdet] at hpos
  norm_num at hpos

private theorem not_isUnit_zero11 :
    ¬ IsUnit (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp

/-- Violated assumption: with singular `V` the GLS Gram is not a unit. -/
theorem bridge_singularV_gram_not_unit :
    ¬ IsUnit (tXᵀ * sV⁻¹ * tX) := by
  have hinv : sV⁻¹ = 0 := by
    rw [Matrix.inv_def, sVdet, Ring.inverse_zero, zero_smul]
  rw [hinv]
  simp only [Matrix.mul_zero, Matrix.zero_mul]
  exact not_isUnit_zero11

/-- Violated assumption: a zero design has a singular GLS Gram. -/
theorem bridge_zeroX_not_unit :
    ¬ IsUnit ((0 : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * tV⁻¹
      * (0 : Matrix (Fin 2) (Fin 1) ℝ)) := by
  rw [show (0 : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * tV⁻¹
      * (0 : Matrix (Fin 2) (Fin 1) ℝ) = 0 from by simp]
  exact not_isUnit_zero11

/-- Violated assumption: the zero design column is not independent. -/
theorem bridge_zeroX_not_independent :
    ¬ LinearIndependent ℝ (0 : Matrix (Fin 2) (Fin 1) ℝ).col := by
  intro h
  exact h.ne_zero 0 (by ext i; simp)

/-- BLUP weights annihilate the design in the example. -/
theorem bridge_blup_annihilates : blupMatrix tX tZ tG tV * tX = 0 :=
  blupMatrix_mul_X hX

/-- The GLS matrix is the identity on the design in the example. -/
theorem bridge_gls_identity : glsMatrix tX tV * tX = 1 :=
  glsMatrix_mul_self hX

/-- BLUP MSE minimality instantiated in the example. -/
theorem bridge_blup_mse (C : Matrix (Fin 1) (Fin 2) ℝ) (hC : C * tX = 0) :
    (mseMatrix tZ tG tV C -
      mseMatrix tZ tG tV (blupMatrix tX tZ tG tV)).PosSemidef :=
  blup_mse_minimality hG hV hX C hC

/-- Mixed-model GLS unbiasedness instantiated in the example. -/
theorem bridge_mixed_unbiased {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (β : Fin 1 → ℝ) {ε : Ω → Fin 2 → ℝ}
    (hint : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) :
    ∫ ω, glsEstimator tX (phenCov tZ tG tR) (tX *ᵥ β + ε ω) ∂μ = β :=
  mixed_glsEstimator_unbiased tX tZ tG tR hXm β hint hmean

/-- Mixed-model GLS covariance instantiated in the example. -/
theorem bridge_mixed_covariance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (β : Fin 1 → ℝ) {ε : Ω → Fin 2 → ℝ}
    (hL2 : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] =
      phenCov tZ tG tR i j) (a b : Fin 1) :
    cov[fun ω => glsEstimator tX (phenCov tZ tG tR) (tX *ᵥ β + ε ω) a,
      fun ω => glsEstimator tX (phenCov tZ tG tR) (tX *ᵥ β + ε ω) b; μ] =
      (tXᵀ * (phenCov tZ tG tR)⁻¹ * tX)⁻¹ a b :=
  mixed_glsEstimator_covariance tX tZ tG tR hG hR hXm β hL2 hcov a b

end MathlibExtTest.GLSBridge
