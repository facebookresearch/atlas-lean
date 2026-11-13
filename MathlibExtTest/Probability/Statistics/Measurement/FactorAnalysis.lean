/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Probability.Statistics.Measurement.FactorAnalysis
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Prod

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Factor analysis tests: one-factor and multi-group combined scope

Tests for one-factor covariance identification (Anderson and Rubin) and
multi-group affine invariance (Wu and Estabrook), including Gaussian bridges,
necessity counterexamples and the joint two-group indeterminacy theorem.
-/

namespace MathlibExt.Probability.Statistics.Measurement.Test

open MathlibExt.Probability.Statistics.Measurement

/-- Loadings `1, 2, 3` on three indicators: all nonzero. -/
public def loadings3 : Fin 3 → ℝ := ![1, 2, 3]

/-- Unit error variances on three indicators. -/
public def variances3 : Fin 3 → ℝ := fun _ => 1

/-- Off-diagonal covariances of the three-indicator example are `2`, `3`, `6`. -/
public theorem offDiag_three :
    oneFactorCovariance loadings3 variances3 0 1 = 2 ∧
      oneFactorCovariance loadings3 variances3 0 2 = 3 ∧
      oneFactorCovariance loadings3 variances3 1 2 = 6 := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have e01 := oneFactorCovariance_offDiag loadings3 variances3 h01
  have e02 := oneFactorCovariance_offDiag loadings3 variances3 h02
  have e12 := oneFactorCovariance_offDiag loadings3 variances3 h12
  simp [loadings3] at e01 e02 e12
  norm_num at e01 e02 e12
  exact ⟨e01, e02, e12⟩

/-- The first squared loading is recovered as `2 * 3 / 6` through the loading
identity. -/
public theorem sq_loading_three :
    loadings3 0 * loadings3 0 =
      oneFactorCovariance loadings3 variances3 0 1 *
        oneFactorCovariance loadings3 variances3 0 2 /
        oneFactorCovariance loadings3 variances3 1 2 := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hb : loadings3 1 ≠ 0 := by norm_num [loadings3]
  have hc : loadings3 2 ≠ 0 := by norm_num [loadings3]
  exact sq_loading_of_oneFactorCovariance loadings3 variances3 0 1 2
    h01 h02 h12 hb hc

/-- All three error variances are positive. -/
public theorem variances3_pos : ∀ i, 0 < variances3 i := by
  intro i
  simp only [variances3]
  norm_num

/-- The three-indicator example is identified up to a global sign. -/
public theorem identified_three : ∀ (l' ψ' : Fin 3 → ℝ),
    oneFactorCovariance l' ψ' =
      oneFactorCovariance loadings3 variances3 →
      (l' = loadings3 ∨ l' = -loadings3) ∧ ψ' = variances3 := by
  intro l' ψ' h
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h0 : loadings3 0 ≠ 0 := by norm_num [loadings3]
  have h1 : loadings3 1 ≠ 0 := by norm_num [loadings3]
  have h2 : loadings3 2 ≠ 0 := by norm_num [loadings3]
  exact eq_or_eq_neg_of_oneFactorCovariance_eq loadings3 variances3 l' ψ'
    0 1 2 h01 h02 h12 h0 h1 h2 h

/-- Loadings `1, 1` on two indicators. -/
public def loadings2 : Fin 2 → ℝ := ![1, 1]

/-- Unit error variances on two indicators. -/
public def variances2 : Fin 2 → ℝ := fun _ => 1

/-- Alternative loadings `5 / 4, 4 / 5` with the same covariance. -/
public noncomputable def loadings2' : Fin 2 → ℝ := ![5 / 4, 4 / 5]

/-- Alternative error variances `7 / 16, 34 / 25` with the same covariance. -/
public noncomputable def variances2' : Fin 2 → ℝ := ![7 / 16, 34 / 25]

/-- Both two-indicator parameter sets give the same covariance (Anderson and
Rubin (1956), Lemma 5.2). -/
public theorem cov_eq_two :
    oneFactorCovariance loadings2' variances2' =
      oneFactorCovariance loadings2 variances2 := by
  ext a b
  fin_cases a <;> fin_cases b
  · simp only [oneFactorCovariance_diag]
    norm_num [loadings2, loadings2', variances2, variances2']
  · have h : (0 : Fin 2) ≠ 1 := by decide
    show oneFactorCovariance loadings2' variances2' 0 1 =
      oneFactorCovariance loadings2 variances2 0 1
    rw [oneFactorCovariance_offDiag _ _ h,
      oneFactorCovariance_offDiag _ _ h]
    norm_num [loadings2, loadings2']
  · have h : (1 : Fin 2) ≠ 0 := by decide
    show oneFactorCovariance loadings2' variances2' 1 0 =
      oneFactorCovariance loadings2 variances2 1 0
    rw [oneFactorCovariance_offDiag _ _ h,
      oneFactorCovariance_offDiag _ _ h]
    norm_num [loadings2, loadings2']
  · simp only [oneFactorCovariance_diag]
    norm_num [loadings2, loadings2', variances2, variances2']

/-- The alternative two-indicator loadings differ from the originals by more
than a global sign. -/
public theorem not_sign_two :
    loadings2' ≠ loadings2 ∧ loadings2' ≠ -loadings2 := by
  constructor
  · intro hcon
    have h0 := congrFun hcon 0
    norm_num [loadings2, loadings2'] at h0
  · intro hcon
    have h0 := congrFun hcon 0
    norm_num [loadings2, loadings2', Pi.neg_apply] at h0

/-- Both alternative two-indicator error variances are positive. -/
public theorem variances2'_pos : ∀ i, 0 < variances2' i := by
  intro i
  fin_cases i <;> norm_num [variances2']

/-- Loadings `1, 1, 0` on three indicators: the last loading is zero. -/
public def loadingsZero : Fin 3 → ℝ := ![1, 1, 0]

/-- Unit error variances on three indicators. -/
public def variancesZero : Fin 3 → ℝ := fun _ => 1

/-- Alternative loadings `5 / 4, 4 / 5, 0` with the same covariance. -/
public noncomputable def loadingsZero' : Fin 3 → ℝ := ![5 / 4, 4 / 5, 0]

/-- Alternative error variances `7 / 16, 34 / 25, 1` with the same covariance. -/
public noncomputable def variancesZero' : Fin 3 → ℝ := ![7 / 16, 34 / 25, 1]

/-- Both zero-loading parameter sets give the same covariance. -/
public theorem cov_eq_zero :
    oneFactorCovariance loadingsZero' variancesZero' =
      oneFactorCovariance loadingsZero variancesZero := by
  ext a b
  fin_cases a <;> fin_cases b
  · simp only [oneFactorCovariance_diag]
    norm_num [loadingsZero, loadingsZero', variancesZero, variancesZero']
  · have h : (0 : Fin 3) ≠ 1 := by decide
    show oneFactorCovariance loadingsZero' variancesZero' 0 1 =
      oneFactorCovariance loadingsZero variancesZero 0 1
    rw [oneFactorCovariance_offDiag _ _ h,
      oneFactorCovariance_offDiag _ _ h]
    norm_num [loadingsZero, loadingsZero']
  · have h : (0 : Fin 3) ≠ 2 := by decide
    show oneFactorCovariance loadingsZero' variancesZero' 0 2 =
      oneFactorCovariance loadingsZero variancesZero 0 2
    rw [oneFactorCovariance_offDiag _ _ h,
      oneFactorCovariance_offDiag _ _ h]
    norm_num [loadingsZero, loadingsZero']
  · have h : (1 : Fin 3) ≠ 0 := by decide
    show oneFactorCovariance loadingsZero' variancesZero' 1 0 =
      oneFactorCovariance loadingsZero variancesZero 1 0
    rw [oneFactorCovariance_offDiag _ _ h,
      oneFactorCovariance_offDiag _ _ h]
    norm_num [loadingsZero, loadingsZero']
  · simp only [oneFactorCovariance_diag]
    norm_num [loadingsZero, loadingsZero', variancesZero, variancesZero']
  · have h : (1 : Fin 3) ≠ 2 := by decide
    show oneFactorCovariance loadingsZero' variancesZero' 1 2 =
      oneFactorCovariance loadingsZero variancesZero 1 2
    rw [oneFactorCovariance_offDiag _ _ h,
      oneFactorCovariance_offDiag _ _ h]
    norm_num [loadingsZero, loadingsZero']
  · have h : (2 : Fin 3) ≠ 0 := by decide
    show oneFactorCovariance loadingsZero' variancesZero' 2 0 =
      oneFactorCovariance loadingsZero variancesZero 2 0
    rw [oneFactorCovariance_offDiag _ _ h,
      oneFactorCovariance_offDiag _ _ h]
    norm_num [loadingsZero, loadingsZero']
  · have h : (2 : Fin 3) ≠ 1 := by decide
    show oneFactorCovariance loadingsZero' variancesZero' 2 1 =
      oneFactorCovariance loadingsZero variancesZero 2 1
    rw [oneFactorCovariance_offDiag _ _ h,
      oneFactorCovariance_offDiag _ _ h]
    norm_num [loadingsZero, loadingsZero']
  · simp only [oneFactorCovariance_diag]
    norm_num [loadingsZero, loadingsZero', variancesZero, variancesZero']

/-- The alternative zero-loading parameters differ from the originals by more
than a global sign. -/
public theorem not_sign_zero :
    loadingsZero' ≠ loadingsZero ∧ loadingsZero' ≠ -loadingsZero := by
  constructor
  · intro hcon
    have h0 := congrFun hcon 0
    norm_num [loadingsZero, loadingsZero'] at h0
  · intro hcon
    have h0 := congrFun hcon 0
    norm_num [loadingsZero, loadingsZero', Pi.neg_apply] at h0

/-- The product of the first two loadings agrees across the two zero-loading
parameter sets. -/
public theorem prod_eq_zero :
    loadingsZero 0 * loadingsZero 1 =
      loadingsZero' 0 * loadingsZero' 1 := by
  norm_num [loadingsZero, loadingsZero']

/-- All three alternative zero-loading error variances are positive. -/
public theorem variancesZero'_pos : ∀ i, 0 < variancesZero' i := by
  intro i
  fin_cases i <;> norm_num [variancesZero']

open MeasureTheory ProbabilityTheory MetaMathlibExt Matrix
open scoped Matrix

/-- Explicit covariance of the three-indicator example. -/
public theorem explicitCov_three :
    oneFactorCovariance loadings3 variances3 =
        !![2, 2, 3; 2, 5, 6; 3, 6, 10] ∧
      oneFactorCovariance loadings3 variances3 =
        loadingColumn loadings3 * (loadingColumn loadings3)ᵀ +
          Matrix.diagonal variances3 := by
  have hmat : oneFactorCovariance loadings3 variances3 =
      !![2, 2, 3; 2, 5, 6; 3, 6, 10] := by
    ext a b
    fin_cases a <;> fin_cases b
    · simp only [oneFactorCovariance_diag]
      norm_num [loadings3, variances3]
    · have h : (0 : Fin 3) ≠ 1 := by decide
      show oneFactorCovariance loadings3 variances3 0 1 = 2
      rw [oneFactorCovariance_offDiag _ _ h]
      norm_num [loadings3]
    · have h : (0 : Fin 3) ≠ 2 := by decide
      show oneFactorCovariance loadings3 variances3 0 2 = 3
      rw [oneFactorCovariance_offDiag _ _ h]
      norm_num [loadings3]
    · have h : (1 : Fin 3) ≠ 0 := by decide
      show oneFactorCovariance loadings3 variances3 1 0 = 2
      rw [oneFactorCovariance_offDiag _ _ h]
      norm_num [loadings3]
    · simp only [oneFactorCovariance_diag]
      norm_num [loadings3, variances3]
    · have h : (1 : Fin 3) ≠ 2 := by decide
      show oneFactorCovariance loadings3 variances3 1 2 = 6
      rw [oneFactorCovariance_offDiag _ _ h]
      norm_num [loadings3]
    · have h : (2 : Fin 3) ≠ 0 := by decide
      show oneFactorCovariance loadings3 variances3 2 0 = 3
      rw [oneFactorCovariance_offDiag _ _ h]
      norm_num [loadings3]
    · have h : (2 : Fin 3) ≠ 1 := by decide
      show oneFactorCovariance loadings3 variances3 2 1 = 6
      rw [oneFactorCovariance_offDiag _ _ h]
      norm_num [loadings3]
    · simp only [oneFactorCovariance_diag]
      norm_num [loadings3, variances3]
  have hcol : oneFactorCovariance loadings3 variances3 =
      loadingColumn loadings3 * (loadingColumn loadings3)ᵀ +
        Matrix.diagonal variances3 := by
    unfold oneFactorCovariance
    rw [loadingColumn_mul_transpose]
  exact ⟨hmat, hcol⟩

/-- Nonvacuity of the bridge on an explicit product space: the factor `F` and
the error `E` are the coordinate projections of
`N(0, 1) ⊗ N(0, diagonal variances3)`, and the observation `X = μ + Λ F + E` of
the three-indicator loading model is defined from them. Every hypothesis of
`gaussian_oneFactor_observation` is discharged: measurability of the
projections, their Gaussian marginals, their independence, the observation
equation and nonnegative error variances. -/
public theorem bridge_nonvacuous (μ : EuclideanSpace ℝ (Fin 3)) :
    Measure.map (fun ω : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
        μ + (WithLp.equiv 2 _).symm
          ((loadingColumn loadings3) *ᵥ ((WithLp.equiv 2 _) ω.1)) + ω.2)
      ((ProbabilityTheory.multivariateGaussian 0 1).prod
        (ProbabilityTheory.multivariateGaussian 0 (Matrix.diagonal variances3)))
    = ProbabilityTheory.multivariateGaussian μ
      (oneFactorCovariance loadings3 variances3) := by
  refine gaussian_oneFactor_observation _ _ Prod.fst Prod.snd μ loadings3 variances3
    measurable_fst measurable_snd ?_ ?_ ?_ (ae_of_all _ fun _ => rfl) ?_
  · rw [Measure.map_fst_prod, measure_univ, one_smul]
  · rw [Measure.map_snd_prod, measure_univ, one_smul]
  · exact indepFun_prod measurable_id measurable_id
  · intro i
    simp [variances3]

/-- The two-indicator loading models have the same observation law although
the loadings differ by more than a sign. -/
public theorem obsLaw_eq_two {O1 O2 : Type*} [MeasurableSpace O1]
    [MeasurableSpace O2]
    (X1 : O1 → EuclideanSpace ℝ (Fin 2))
    (X2 : O2 → EuclideanSpace ℝ (Fin 2))
    (P1 : Measure O1) (P2 : Measure O2)
    (μ : EuclideanSpace ℝ (Fin 2))
    (h1 : Measure.map X1 P1 = ProbabilityTheory.multivariateGaussian μ
      (oneFactorCovariance loadings2 variances2))
    (h2 : Measure.map X2 P2 = ProbabilityTheory.multivariateGaussian μ
      (oneFactorCovariance loadings2' variances2')) :
    Measure.map X1 P1 = Measure.map X2 P2 := by
  exact obsLaw_eq_of_oneFactorCovariance_eq X1 X2 P1 P2 μ loadings2
    variances2 loadings2' variances2' h1 h2 cov_eq_two

/-- The zero-loading models have the same observation law although
the loadings differ by more than a sign. -/
public theorem obsLaw_eq_zero {O1 O2 : Type*} [MeasurableSpace O1]
    [MeasurableSpace O2]
    (X1 : O1 → EuclideanSpace ℝ (Fin 3))
    (X2 : O2 → EuclideanSpace ℝ (Fin 3))
    (P1 : Measure O1) (P2 : Measure O2)
    (μ : EuclideanSpace ℝ (Fin 3))
    (h1 : Measure.map X1 P1 = ProbabilityTheory.multivariateGaussian μ
      (oneFactorCovariance loadingsZero variancesZero))
    (h2 : Measure.map X2 P2 = ProbabilityTheory.multivariateGaussian μ
      (oneFactorCovariance loadingsZero' variancesZero')) :
    Measure.map X1 P1 = Measure.map X2 P2 := by
  exact obsLaw_eq_of_oneFactorCovariance_eq X1 X2 P1 P2 μ loadingsZero
    variancesZero loadingsZero' variancesZero' h1 h2 cov_eq_zero

/-- Example 2-by-1 loading matrix with all entries `1`. -/
public def loadingMat2x1 : Matrix (Fin 2) (Fin 1) ℝ := loadingColumn ![1, 1]

public theorem trans_one :
    (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ
      ((![0] : Fin 1 → ℝ) - ![-1]) = ![1] := by
  rw [inv_one, Matrix.one_mulVec]
  ext i
  fin_cases i
  norm_num [Pi.sub_apply]

public theorem trans_zero :
    (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ
      ((![0] : Fin 1 → ℝ) - 0) = ![0] := by
  rw [inv_one, Matrix.one_mulVec, sub_zero]

public theorem vec_one_ne_zero : (![1] : Fin 1 → ℝ) ≠ ![0] := by
  intro hcon
  have h0 := congrFun hcon 0
  norm_num at h0

/-- Group 1 Gaussian law is unchanged under `U = 1`, `β = ![-1]` (via
`multivariateGaussian_factorModel_transform`). -/
public theorem group1_law_unchanged :
    ProbabilityTheory.multivariateGaussian
        ((WithLp.equiv 2 _).symm
          (factorModelMean (0 : Fin 2 → ℝ) loadingMat2x1 ![0]))
        (factorModelCov loadingMat2x1 1 1)
      = ProbabilityTheory.multivariateGaussian
        ((WithLp.equiv 2 _).symm
          (factorModelMean ((0 : Fin 2 → ℝ) + loadingMat2x1 *ᵥ ![-1])
            (loadingMat2x1 * (1 : Matrix (Fin 1) (Fin 1) ℝ))
            ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ
              ((![0] : Fin 1 → ℝ) - ![-1]))))
        (factorModelCov (loadingMat2x1 * (1 : Matrix (Fin 1) (Fin 1) ℝ))
          ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * 1 *
            (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ᵀ) 1) := by
  have hU : IsUnit (1 : Matrix (Fin 1) (Fin 1) ℝ).det := by
    rw [Matrix.det_one]
    exact isUnit_one
  exact multivariateGaussian_factorModel_transform loadingMat2x1 0 ![0]
    1 1 1 ![-1] hU

/-- Group 2 Gaussian law is unchanged under `U = 1`, `β = 0` (via
`multivariateGaussian_factorModel_transform`). -/
public theorem group2_law_unchanged :
    ProbabilityTheory.multivariateGaussian
        ((WithLp.equiv 2 _).symm
          (factorModelMean (0 : Fin 2 → ℝ) loadingMat2x1 ![0]))
        (factorModelCov loadingMat2x1 1 1)
      = ProbabilityTheory.multivariateGaussian
        ((WithLp.equiv 2 _).symm
          (factorModelMean ((0 : Fin 2 → ℝ) +
            loadingMat2x1 *ᵥ (0 : Fin 1 → ℝ))
            (loadingMat2x1 * (1 : Matrix (Fin 1) (Fin 1) ℝ))
            ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ
              ((![0] : Fin 1 → ℝ) - 0))))
        (factorModelCov (loadingMat2x1 * (1 : Matrix (Fin 1) (Fin 1) ℝ))
          ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * 1 *
            (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ᵀ) 1) := by
  have hU : IsUnit (1 : Matrix (Fin 1) (Fin 1) ℝ).det := by
    rw [Matrix.det_one]
    exact isUnit_one
  exact multivariateGaussian_factorModel_transform loadingMat2x1 0 ![0]
    1 1 1 0 hU

public def a_ex : Fin 2 → (Fin 1 → ℝ) := fun _ => ![0]

public def U_ex : Fin 2 → Matrix (Fin 1) (Fin 1) ℝ := fun _ => 1

public def b_ex : Fin 2 → (Fin 1 → ℝ) := ![![-1], ![0]]

/-- Original factor means agree, but transformed means `![1]` and `![0]`
differ: latent comparisons change without invariance. The per-group laws are
`multivariateGaussian_factorModel_transform`. -/
public theorem means_agree_transformed_differ :
    (∀ g, ProbabilityTheory.multivariateGaussian
          ((WithLp.equiv 2 _).symm
            (factorModelMean (0 : Fin 2 → ℝ) loadingMat2x1 (a_ex g)))
          (factorModelCov loadingMat2x1 1 1)
        = ProbabilityTheory.multivariateGaussian
          ((WithLp.equiv 2 _).symm
            (factorModelMean ((0 : Fin 2 → ℝ) + loadingMat2x1 *ᵥ b_ex g)
              (loadingMat2x1 * U_ex g)
              ((U_ex g)⁻¹ *ᵥ (a_ex g - b_ex g))))
          (factorModelCov (loadingMat2x1 * U_ex g)
            ((U_ex g)⁻¹ * 1 * (U_ex g)⁻¹ᵀ) 1))
      ∧ a_ex 0 = a_ex 1
      ∧ (U_ex 0)⁻¹ *ᵥ (a_ex 0 - b_ex 0) = (![1] : Fin 1 → ℝ)
      ∧ (U_ex 1)⁻¹ *ᵥ (a_ex 1 - b_ex 1) = (![0] : Fin 1 → ℝ)
      ∧ (U_ex 0)⁻¹ *ᵥ (a_ex 0 - b_ex 0) ≠
        (U_ex 1)⁻¹ *ᵥ (a_ex 1 - b_ex 1) := by
  have hU : ∀ g, IsUnit (U_ex g).det := by
    intro g
    simp only [U_ex, Matrix.det_one]
    exact isUnit_one
  have hEq : a_ex 0 = a_ex 1 := rfl
  have htrans0 : (U_ex 0)⁻¹ *ᵥ (a_ex 0 - b_ex 0) = (![1] : Fin 1 → ℝ) := by
    simp only [a_ex, U_ex, b_ex, Matrix.cons_val_zero]
    exact trans_one
  have htrans1 : (U_ex 1)⁻¹ *ᵥ (a_ex 1 - b_ex 1) = (![0] : Fin 1 → ℝ) := by
    simp only [a_ex, U_ex, b_ex, Matrix.cons_val_one, Matrix.cons_val_zero]
    -- reduce to the shared computation with `0` target
    have hzz : ((![0] : Fin 1 → ℝ) - ![0]) = ((![0] : Fin 1 → ℝ) - 0) := by
      have h0 : (![0] : Fin 1 → ℝ) - ![0] = ![0] := by
        ext i
        fin_cases i
        norm_num [Pi.sub_apply]
      rw [h0, sub_zero]
    rw [hzz]
    exact trans_zero
  have hNe : (U_ex 0)⁻¹ *ᵥ (a_ex 0 - b_ex 0) ≠
      (U_ex 1)⁻¹ *ᵥ (a_ex 1 - b_ex 1) := by
    rw [htrans0, htrans1]
    exact vec_one_ne_zero
  have hlaws := fun g => multivariateGaussian_factorModel_transform loadingMat2x1
    (0 : Fin 2 → ℝ) (a_ex g) 1 1 (U_ex g) (b_ex g) (hU g)
  exact ⟨hlaws, hEq, htrans0, htrans1, hNe⟩

/-- `twoGroup_affine_indeterminacy` on the 2-by-1 example with the common factor
mean `![0]`: it supplies invertible group-specific transforms that keep both
groups' Gaussian laws and give unequal transformed means. -/
public theorem twoGroup_indeterminacy_example :
    ∃ (U : Fin 2 → Matrix (Fin 1) (Fin 1) ℝ) (β : Fin 2 → (Fin 1 → ℝ)),
      (∀ g, IsUnit (U g).det) ∧
      (∀ g, ProbabilityTheory.multivariateGaussian
          ((WithLp.equiv 2 _).symm
            (factorModelMean (0 : Fin 2 → ℝ) loadingMat2x1 ![0]))
          (factorModelCov loadingMat2x1 1 1)
        = ProbabilityTheory.multivariateGaussian
          ((WithLp.equiv 2 _).symm
            (factorModelMean ((0 : Fin 2 → ℝ) + loadingMat2x1 *ᵥ β g)
              (loadingMat2x1 * U g) ((U g)⁻¹ *ᵥ (![0] - β g))))
          (factorModelCov (loadingMat2x1 * U g) ((U g)⁻¹ * 1 * (U g)⁻¹ᵀ) 1)) ∧
      (U 0)⁻¹ *ᵥ ((![0] : Fin 1 → ℝ) - β 0) ≠ (U 1)⁻¹ *ᵥ (![0] - β 1) :=
  twoGroup_affine_indeterminacy loadingMat2x1 0 ![0] 1 1

/-- With zero loadings, common loadings and intercepts hold yet transformed
means differ: injectivity in `transform_eq_of_common` is necessary. -/
public theorem zero_loading_necessity :
    (0 : Matrix (Fin 2) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) =
        (0 : Matrix (Fin 2) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) ∧
      (0 : Fin 2 → ℝ) + (0 : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ ![-1] =
        (0 : Fin 2 → ℝ) + (0 : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ 0 ∧
      (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ
          ((![0] : Fin 1 → ℝ) - ![-1]) ≠
        (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ
          ((![0] : Fin 1 → ℝ) - 0) ∧
      ¬ Function.Injective (0 : Matrix (Fin 2) (Fin 1) ℝ).mulVec ∧
      (![-1] : Fin 1 → ℝ) ≠ 0 := by
  have htrans : (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ
      ((![0] : Fin 1 → ℝ) - ![-1]) ≠
      (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ
        ((![0] : Fin 1 → ℝ) - 0) := by
    rw [trans_one, trans_zero]
    exact vec_one_ne_zero
  have hnot : ¬ Function.Injective
      (0 : Matrix (Fin 2) (Fin 1) ℝ).mulVec := by
    intro hinj
    have h0 : (0 : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ (![0] : Fin 1 → ℝ) =
        (0 : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ (![1] : Fin 1 → ℝ) := by
      simp
    have hcon := hinj h0
    have h1 : (![0] : Fin 1 → ℝ) ≠ ![1] := by
      intro hc
      have hc0 := congrFun hc 0
      norm_num at hc0
    exact h1 hcon
  have hbeta : (![-1] : Fin 1 → ℝ) ≠ 0 := by
    intro hcon
    have h0 := congrFun hcon 0
    norm_num at h0
  refine ⟨rfl, by simp, htrans, hnot, hbeta⟩

/-- Singular `U = 0` changes the covariance: left `1`, right
`!![2, 1; 1, 2]`; invertibility in `factorModelCov_transform` is
necessary. -/
public theorem singular_cov_changes :
    factorModelCov ((1 : Matrix (Fin 2) (Fin 2) ℝ) * 0)
        ((0 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * !![1, 1; 1, 1] *
          (0 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ᵀ) 1 = 1 ∧
      factorModelCov (1 : Matrix (Fin 2) (Fin 2) ℝ) !![1, 1; 1, 1] 1 =
        !![2, 1; 1, 2] ∧
      factorModelCov ((1 : Matrix (Fin 2) (Fin 2) ℝ) * 0)
          ((0 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * !![1, 1; 1, 1] *
            (0 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ᵀ) 1 ≠
        factorModelCov (1 : Matrix (Fin 2) (Fin 2) ℝ) !![1, 1; 1, 1]
          1 := by
  have hleft : factorModelCov ((1 : Matrix (Fin 2) (Fin 2) ℝ) * 0)
      ((0 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * !![1, 1; 1, 1] *
        (0 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ᵀ) 1 = 1 := by
    unfold factorModelCov
    simp
  have hright : factorModelCov (1 : Matrix (Fin 2) (Fin 2) ℝ)
      !![1, 1; 1, 1] 1 = !![2, 1; 1, 2] := by
    unfold factorModelCov
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.transpose_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply] <;> norm_num
  have hne : (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠ !![2, 1; 1, 2] := by
    intro hcon
    have h0 := congrFun (congrFun hcon 0) 0
    norm_num at h0
  refine ⟨hleft, hright, by rw [hleft, hright]; exact hne⟩

/-- Swap rotation preserves the covariance (via
`factorModelCov_mul_orthogonal`). -/
public theorem swap_preserves_cov :
    factorModelCov ((1 : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 1; 1, 0]) 1 1 =
      factorModelCov (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
  have hU : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.transpose_apply]
  exact factorModelCov_mul_orthogonal 1 1 !![0, 1; 1, 0] hU

/-- With injective loadings, common loadings and intercepts determine the
affine transform and transformed mean comparisons agree with original ones:
the compatible-constraint hypotheses hold together (positive counterpart to
the zero-loading necessity test). -/
public theorem injective_positive :
    (∀ (U1 U2 : Matrix (Fin 1) (Fin 1) ℝ) (b1 b2 : Fin 1 → ℝ)
        (_hU1 : IsUnit U1.det) (_hU2 : IsUnit U2.det)
        (_hU : (1 : Matrix (Fin 1) (Fin 1) ℝ) * U1 = 1 * U2)
        (_hb : (0 : Fin 1 → ℝ) + 1 *ᵥ b1 = 0 + 1 *ᵥ b2),
        U1 = U2 ∧ b1 = b2) ∧
      (∀ (a1 a2 : Fin 1 → ℝ),
        (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ (a1 - 0) =
            (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ (a2 - 0) ↔
          a1 = a2) := by
  have hΛ : Function.Injective
      (1 : Matrix (Fin 1) (Fin 1) ℝ).mulVec := by
    have h1 : IsUnit (1 : Matrix (Fin 1) (Fin 1) ℝ) := isUnit_one
    exact Matrix.mulVec_injective_iff_isUnit.mpr h1
  have hUnit : IsUnit (1 : Matrix (Fin 1) (Fin 1) ℝ).det := by
    rw [Matrix.det_one]
    exact isUnit_one
  have hU : (1 : Matrix (Fin 1) (Fin 1) ℝ) * 1 = 1 * 1 := rfl
  have hb : (0 : Fin 1 → ℝ) + (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ 0 =
      0 + 1 *ᵥ (0 : Fin 1 → ℝ) := rfl
  constructor
  · intro U1 U2 b1 b2 hU1' hU2' hU' hb'
    exact transform_eq_of_common hΛ hU1' hU2' hU' hb'
  · intro a1 a2
    exact transformedMeans_agree_iff_of_common 1 0 a1 a2 0 0 1 1 hΛ
      hUnit hUnit hU hb

end MathlibExt.Probability.Statistics.Measurement.Test
