/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import MathlibExt.Probability.Distributions.GaussianConditioning
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Independence.Basic

import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Factor analysis: one-factor identification and multi-group indeterminacy

Standardized one-factor covariance model after Anderson and Rubin (1956):
covariance entries, loading and noise recovery identities, and identification
of loadings up to a global sign with equal error variances. Gaussian
loading-model bridge connecting the psychometric model to its observation law.
Multi-group linear factor model after Wu and Estabrook (2016): affine
reparametrization invariance of means, covariances and Gaussian laws, with
strong-invariance constraints identifying the transform.
-/

namespace MathlibExt.Probability.Statistics.Measurement

@[expose] public section

/-- Covariance matrix implied by the standardized one-factor model with loadings
`l` and error variances `ψ`: the outer product of the loadings plus the diagonal
error-variance matrix (Anderson and Rubin (1956), equation (3.1) with one factor). -/
public def oneFactorCovariance {ι : Type*} [DecidableEq ι] (l ψ : ι → ℝ) :
    Matrix ι ι ℝ :=
  Matrix.vecMulVec l l + Matrix.diagonal ψ

/-- Off-diagonal entries of the one-factor covariance are products of loadings. -/
public theorem oneFactorCovariance_offDiag {ι : Type*} [DecidableEq ι]
    (l ψ : ι → ℝ) {a b : ι} (hab : a ≠ b) :
    oneFactorCovariance l ψ a b = l a * l b := by
  have hdiag : Matrix.diagonal ψ a b = 0 := Matrix.diagonal_apply_ne _ hab
  unfold oneFactorCovariance
  rw [Matrix.add_apply, Matrix.vecMulVec_apply, hdiag, add_zero]

/-- Diagonal entries of the one-factor covariance are squared loadings plus the
error variance. -/
public theorem oneFactorCovariance_diag {ι : Type*} [DecidableEq ι]
    (l ψ : ι → ℝ) (a : ι) :
    oneFactorCovariance l ψ a a = l a * l a + ψ a := by
  have hdiag : Matrix.diagonal ψ a a = ψ a := Matrix.diagonal_apply_eq _ _
  unfold oneFactorCovariance
  rw [Matrix.add_apply, Matrix.vecMulVec_apply, hdiag]

/-- A squared loading is recovered from three off-diagonal covariances (the
rank argument for one factor behind Anderson and Rubin (1956), Theorem 5.1). -/
public theorem sq_loading_of_oneFactorCovariance {ι : Type*} [DecidableEq ι]
    (l ψ : ι → ℝ) (a b c : ι)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hb : l b ≠ 0) (hc : l c ≠ 0) :
    l a * l a = oneFactorCovariance l ψ a b * oneFactorCovariance l ψ a c /
      oneFactorCovariance l ψ b c := by
  have hne : l b * l c ≠ 0 := mul_ne_zero hb hc
  rw [oneFactorCovariance_offDiag l ψ hab, oneFactorCovariance_offDiag l ψ hac,
    oneFactorCovariance_offDiag l ψ hbc, eq_div_iff hne]
  ring

/-- An error variance is the diagonal entry minus the recovered squared loading. -/
public theorem noise_of_oneFactorCovariance {ι : Type*} [DecidableEq ι]
    (l ψ : ι → ℝ) (a : ι) :
    ψ a = oneFactorCovariance l ψ a a - l a * l a := by
  have e := oneFactorCovariance_diag l ψ a
  rw [e]
  ring

private theorem offDiag_mul_of_cov_eq {ι : Type*} [DecidableEq ι]
    (l ψ l' ψ' : ι → ℝ)
    (h : oneFactorCovariance l' ψ' = oneFactorCovariance l ψ) {a b : ι}
    (hab : a ≠ b) : l' a * l' b = l a * l b := by
  have e1 := oneFactorCovariance_offDiag l' ψ' hab
  have e2 := oneFactorCovariance_offDiag l ψ hab
  have ceq : oneFactorCovariance l' ψ' a b = oneFactorCovariance l ψ a b := by
    rw [h]
  rw [← e1, ← e2]
  exact ceq

private theorem noise_of_cov_eq_of_sq {ι : Type*} [DecidableEq ι]
    (l ψ l' ψ' : ι → ℝ)
    (h : oneFactorCovariance l' ψ' = oneFactorCovariance l ψ)
    (hsq : ∀ t, l' t * l' t = l t * l t) : ψ' = ψ := by
  funext t
  have e1 := oneFactorCovariance_diag l' ψ' t
  have e2 := oneFactorCovariance_diag l ψ t
  have ceq : oneFactorCovariance l' ψ' t t = oneFactorCovariance l ψ t t := by
    rw [h]
  rw [e1, e2, hsq t] at ceq
  exact add_left_cancel ceq

private theorem eq_or_eq_neg_of_mul_self_eq {x y : ℝ} (h : x * x = y * y) :
    x = y ∨ x = -y := by
  have hfac : (x - y) * (x + y) = x * x - y * y := by ring
  rw [h, sub_self] at hfac
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_iff_add_eq_zero.mpr h2)

/-- Identification up to a global sign (Anderson and Rubin (1956), Theorem 5.5,
sufficiency): with three nonzero loadings, equal covariances force equal
loadings up to one shared sign flip and equal error variances. -/
public theorem eq_or_eq_neg_of_oneFactorCovariance_eq {ι : Type*}
    [DecidableEq ι] (l ψ l' ψ' : ι → ℝ) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : l i ≠ 0) (hj : l j ≠ 0) (hk : l k ≠ 0)
    (h : oneFactorCovariance l' ψ' = oneFactorCovariance l ψ) :
    (l' = l ∨ l' = -l) ∧ ψ' = ψ := by
  have hpij : l' i * l' j = l i * l j :=
    offDiag_mul_of_cov_eq l ψ l' ψ' h hij
  have hpik : l' i * l' k = l i * l k :=
    offDiag_mul_of_cov_eq l ψ l' ψ' h hik
  have hpjk : l' j * l' k = l j * l k :=
    offDiag_mul_of_cov_eq l ψ l' ψ' h hjk
  have hlij : l i * l j ≠ 0 := mul_ne_zero hi hj
  have hlik : l i * l k ≠ 0 := mul_ne_zero hi hk
  have hljk : l j * l k ≠ 0 := mul_ne_zero hj hk
  have hi' : l' i ≠ 0 := by
    intro hcon
    rw [hcon, zero_mul] at hpij
    exact hlij hpij.symm
  have hj' : l' j ≠ 0 := by
    intro hcon
    rw [hcon, zero_mul] at hpjk
    exact hljk hpjk.symm
  have hk' : l' k ≠ 0 := by
    intro hcon
    rw [hcon, mul_zero] at hpjk
    exact hljk hpjk.symm
  have hsq_i : l' i * l' i = l i * l i := by
    have e1 := sq_loading_of_oneFactorCovariance l' ψ' i j k hij hik hjk hj' hk'
    have e2 := sq_loading_of_oneFactorCovariance l ψ i j k hij hik hjk hj hk
    have c1 : oneFactorCovariance l' ψ' i j = oneFactorCovariance l ψ i j := by
      rw [h]
    have c2 : oneFactorCovariance l' ψ' i k = oneFactorCovariance l ψ i k := by
      rw [h]
    have c3 : oneFactorCovariance l' ψ' j k = oneFactorCovariance l ψ j k := by
      rw [h]
    rw [e1, c1, c2, c3]
    exact e2.symm
  rcases eq_or_eq_neg_of_mul_self_eq hsq_i with si | si
  · have hall : ∀ t, l' t = l t := by
      intro t
      by_cases hti : t = i
      · subst hti
        exact si
      · have hpt : l' t * l' i = l t * l i :=
          offDiag_mul_of_cov_eq l ψ l' ψ' h hti
        rw [si] at hpt
        exact mul_right_cancel₀ hi hpt
    refine ⟨Or.inl (funext hall),
      noise_of_cov_eq_of_sq l ψ l' ψ' h (fun t => by rw [hall t])⟩
  · have hall : ∀ t, l' t = -(l t) := by
      intro t
      by_cases hti : t = i
      · subst hti
        exact si
      · have hpt : l' t * l' i = l t * l i :=
          offDiag_mul_of_cov_eq l ψ l' ψ' h hti
        rw [si, mul_neg] at hpt
        have h6 : l' t * l i = -(l t * l i) := by
          have h7 := congrArg Neg.neg hpt
          rwa [neg_neg] at h7
        have h2 : l' t * l i = -(l t) * l i := by
          rw [h6, neg_mul]
        exact mul_right_cancel₀ hi h2
    have hfun : l' = -l := funext fun t => by
      rw [Pi.neg_apply]
      exact hall t
    refine ⟨Or.inr hfun,
      noise_of_cov_eq_of_sq l ψ l' ψ' h (fun t => by rw [hall t]; ring)⟩

/-- Identification with one loading sign fixed: adding a positive sign on one
loading to the hypotheses above determines the loadings exactly. -/
public theorem eq_of_oneFactorCovariance_eq_of_pos {ι : Type*}
    [DecidableEq ι] (l ψ l' ψ' : ι → ℝ) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hj : l j ≠ 0) (hk : l k ≠ 0)
    (hpos : 0 < l i) (hpos' : 0 < l' i)
    (h : oneFactorCovariance l' ψ' = oneFactorCovariance l ψ) :
    l' = l ∧ ψ' = ψ := by
  have hi : l i ≠ 0 := ne_of_gt hpos
  obtain ⟨hsign, hψ⟩ := eq_or_eq_neg_of_oneFactorCovariance_eq l ψ l' ψ' i j k
    hij hik hjk hi hj hk h
  refine ⟨?_, hψ⟩
  rcases hsign with heq | hneg
  · exact heq
  · exfalso
    have hci := congrFun hneg i
    simp only [Pi.neg_apply] at hci
    have hneg' : l' i < 0 := by
      rw [hci]
      exact neg_lt_zero.mpr hpos
    exact not_lt_of_ge hpos'.le hneg'

/-- Work-item form of identification up to sign: with at least three indicators
and all loadings nonzero, equal covariances force equal loadings up to one
shared sign flip and equal error variances. -/
public theorem eq_or_eq_neg_of_oneFactorCovariance_eq_of_all_ne {ι : Type*}
    [DecidableEq ι] (l ψ l' ψ' : ι → ℝ) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hall : ∀ t, l t ≠ 0)
    (h : oneFactorCovariance l' ψ' = oneFactorCovariance l ψ) :
    (l' = l ∨ l' = -l) ∧ ψ' = ψ :=
  eq_or_eq_neg_of_oneFactorCovariance_eq l ψ l' ψ' i j k hij hik hjk
    (hall i) (hall j) (hall k) h

open MeasureTheory ProbabilityTheory MetaMathlibExt Matrix
open scoped Matrix

/-- Loading matrix of the one-factor model: the column of loadings `l`
as a matrix with one column (Anderson and Rubin (1956), Section 2, (2.1)). -/
public def loadingColumn {ι : Type*} (l : ι → ℝ) : Matrix ι (Fin 1) ℝ :=
  Matrix.of fun i _ => l i

/-- The loading column times its transpose is the outer product of loadings. -/
public theorem loadingColumn_mul_transpose {ι : Type*} (l : ι → ℝ) :
    loadingColumn l * (loadingColumn l)ᵀ = Matrix.vecMulVec l l := by
  ext i j
  simp [loadingColumn, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.vecMulVec_apply, Matrix.of_apply]

/-- The observation `X = Λ F + μ + E` of the one-factor loading model is
Gaussian with mean `μ` and covariance `oneFactorCovariance l ψ` (Anderson
and Rubin (1956), (3.1)); the law depends on `(l, ψ)` only through that
covariance, so it does not identify the loadings by itself (see
`eq_or_eq_neg_of_oneFactorCovariance_eq` for identification up to sign). -/
public theorem gaussian_oneFactor_observation {ι : Type*} [Fintype ι]
    [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → EuclideanSpace ℝ ι)
    (F : Ω → EuclideanSpace ℝ (Fin 1)) (E : Ω → EuclideanSpace ℝ ι)
    (μ : EuclideanSpace ℝ ι) (l ψ : ι → ℝ)
    (hFm : Measurable F) (hEm : Measurable E)
    (hF : Measure.map F P = ProbabilityTheory.multivariateGaussian 0 1)
    (hE : Measure.map E P =
      ProbabilityTheory.multivariateGaussian 0 (Matrix.diagonal ψ))
    (hindep : IndepFun F E P)
    (hX : ∀ᵐ ω ∂P, X ω = μ + (WithLp.equiv 2 _).symm
      ((loadingColumn l) *ᵥ ((WithLp.equiv 2 _) (F ω))) + E ω)
    (_hψ : ∀ i, 0 ≤ ψ i) :
    Measure.map X P =
      ProbabilityTheory.multivariateGaussian μ (oneFactorCovariance l ψ) := by
  have hS : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef :=
    Matrix.PosSemidef.one
  have hQ : (Matrix.diagonal ψ).PosSemidef :=
    Matrix.PosSemidef.diagonal _hψ
  have hEmw : Measurable (fun ω => μ + E ω) := (measurable_const_add μ).comp hEm
  have hEμ : Measure.map (fun ω => μ + E ω) P =
      ProbabilityTheory.multivariateGaussian μ (Matrix.diagonal ψ) := by
    have hmap := Measure.map_map (measurable_const_add μ) hEm (μ := P)
    rw [hE] at hmap
    rw [MetaMathlibExt.map_add_multivariateGaussian, add_zero] at hmap
    exact hmap.symm
  have hindep2 : IndepFun F (fun ω => μ + E ω) P :=
    hindep.comp measurable_id (measurable_const_add μ)
  have hmain : Measure.map
      (fun ω => (Matrix.toEuclideanLin (loadingColumn l)) (F ω) + (μ + E ω)) P
      = ProbabilityTheory.multivariateGaussian
        ((Matrix.toEuclideanLin (loadingColumn l)) 0 + μ)
        (loadingColumn l * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (loadingColumn l)ᵀ +
          Matrix.diagonal ψ) :=
    MetaMathlibExt.map_linear_add_of_indepFun (x := F)
      (w := fun ω => μ + E ω) hFm hEmw hindep2 hS hQ hF hEμ (loadingColumn l)
  have hmean : (Matrix.toEuclideanLin (loadingColumn l)) 0 + μ = μ := by
    rw [map_zero, zero_add]
  have hcov : loadingColumn l * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
      (loadingColumn l)ᵀ + Matrix.diagonal ψ
      = oneFactorCovariance l ψ := by
    unfold oneFactorCovariance
    rw [Matrix.mul_one, loadingColumn_mul_transpose]
  have hX' : ∀ᵐ ω ∂P, X ω = (Matrix.toEuclideanLin (loadingColumn l)) (F ω) +
      (μ + E ω) := by
    filter_upwards [hX] with ω hω
    have hconv : (Matrix.toEuclideanLin (loadingColumn l)) (F ω) =
        (WithLp.equiv 2 _).symm
          ((loadingColumn l) *ᵥ ((WithLp.equiv 2 _) (F ω))) := by
      simp only [WithLp.equiv_apply, WithLp.equiv_symm_apply,
        Matrix.toLpLin_apply]
    rw [hω, hconv]
    abel
  rw [Measure.map_congr hX', hmain, hmean, hcov]

/-- Two one-factor loading models with the same covariance have the same
observation law (no uniqueness claim for loadings). -/
public theorem obsLaw_eq_of_oneFactorCovariance_eq {ι : Type*} [Fintype ι]
    [DecidableEq ι] {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (X₁ : Ω₁ → EuclideanSpace ℝ ι) (X₂ : Ω₂ → EuclideanSpace ℝ ι)
    (P1 : Measure Ω₁) (P2 : Measure Ω₂)
    (μ : EuclideanSpace ℝ ι) (l ψ l' ψ' : ι → ℝ)
    (h₁ : Measure.map X₁ P1 =
      ProbabilityTheory.multivariateGaussian μ (oneFactorCovariance l ψ))
    (h₂ : Measure.map X₂ P2 =
      ProbabilityTheory.multivariateGaussian μ (oneFactorCovariance l' ψ'))
    (h : oneFactorCovariance l' ψ' = oneFactorCovariance l ψ) :
    Measure.map X₁ P1 = Measure.map X₂ P2 := by
  rw [h₁, h₂, h]

/-- Mean implied by the factor model with intercepts `ν`, loadings `Λ` and
factor means `a`: `ν + Λ *ᵥ a` (Wu and Estabrook (2016), Section 2.1,
(1): `μ = ν + Λκ`). -/
public def factorModelMean {ι κ : Type*} [Fintype κ] (ν : ι → ℝ)
    (Λ : Matrix ι κ ℝ) (a : κ → ℝ) : ι → ℝ :=
  ν + Λ *ᵥ a

/-- Covariance implied by the factor model with loadings `Λ`, factor
covariance `Φ` and error covariance `Θ`: `Λ * Φ * Λᵀ + Θ` (Wu and
Estabrook (2016), Section 2.1, (1): `Σ = ΛΦΛ' + Θ`). -/
public def factorModelCov {ι κ : Type*} [Fintype κ] (Λ : Matrix ι κ ℝ)
    (Φ : Matrix κ κ ℝ) (Θ : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Λ * Φ * Λᵀ + Θ

/-- Affine reparametrization preserves the factor-model mean (Wu and
Estabrook (2016), Section 3.1, (2)): with `Λ̃ = ΛU`, `ν̃ = ν + Λβ` and
`κ̃ = U⁻¹(κ - β)`, the mean is unchanged. -/
public theorem factorModelMean_transform {ι κ : Type*} [Fintype κ]
    [DecidableEq κ] (Λ : Matrix ι κ ℝ) (ν : ι → ℝ) (a : κ → ℝ)
    (U : Matrix κ κ ℝ) (β : κ → ℝ) (hU : IsUnit U.det) :
    factorModelMean (ν + Λ *ᵥ β) (Λ * U) (U⁻¹ *ᵥ (a - β))
      = factorModelMean ν Λ a := by
  unfold factorModelMean
  have hU' : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hU
  have h2 : U *ᵥ (U⁻¹ *ᵥ (a - β)) = (a - β) := by
    rw [Matrix.mulVec_mulVec, hU', Matrix.one_mulVec]
  have hcancel : (Λ * U) *ᵥ (U⁻¹ *ᵥ (a - β)) = Λ *ᵥ (a - β) := by
    rw [← Matrix.mulVec_mulVec, h2]
  rw [hcancel, Matrix.mulVec_sub, add_assoc, add_sub_cancel]

/-- Affine reparametrization preserves the factor-model covariance (Wu and
Estabrook (2016), Section 3.1, (2)): with `Λ̃ = ΛU` and
`Φ̃ = U⁻¹ΦU⁻¹'`, the covariance is unchanged. -/
public theorem factorModelCov_transform {ι κ : Type*} [Fintype κ]
    [DecidableEq κ] (Λ : Matrix ι κ ℝ) (Φ : Matrix κ κ ℝ)
    (Θ : Matrix ι ι ℝ) (U : Matrix κ κ ℝ) (hU : IsUnit U.det) :
    factorModelCov (Λ * U) (U⁻¹ * Φ * U⁻¹ᵀ) Θ
      = factorModelCov Λ Φ Θ := by
  unfold factorModelCov
  have hU' : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hU
  have hUt : U⁻¹ᵀ * Uᵀ = 1 := by
    rw [← Matrix.transpose_mul, hU', Matrix.transpose_one]
  have e1 : (Λ * U) * (U⁻¹ * Φ * U⁻¹ᵀ) = Λ * (Φ * U⁻¹ᵀ) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc U (U⁻¹ * Φ) U⁻¹ᵀ,
      ← Matrix.mul_assoc U U⁻¹ Φ, hU', Matrix.one_mul]
  have e2 : (Φ * U⁻¹ᵀ) * (Uᵀ * Λᵀ) = Φ * Λᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc U⁻¹ᵀ Uᵀ Λᵀ, hUt,
      Matrix.one_mul]
  rw [Matrix.transpose_mul, e1, Matrix.mul_assoc, e2, Matrix.mul_assoc]

/-- Orthogonal rotation preserves the factor-model covariance with `Φ = 1`
(Wu and Estabrook (2016), Section 3.1; D03.2): if `U * Uᵀ = 1`, then `ΛU`
gives the same covariance as `Λ`. -/
public theorem factorModelCov_mul_orthogonal {ι κ : Type*} [Fintype κ]
    [DecidableEq κ] (Λ : Matrix ι κ ℝ) (Θ : Matrix ι ι ℝ)
    (U : Matrix κ κ ℝ) (hU : U * Uᵀ = 1) :
    factorModelCov (Λ * U) 1 Θ = factorModelCov Λ 1 Θ := by
  unfold factorModelCov
  rw [Matrix.transpose_mul, Matrix.mul_one, Matrix.mul_assoc,
    ← Matrix.mul_assoc U Uᵀ Λᵀ, hU, Matrix.one_mul, Matrix.mul_one]

/-- Affine reparametrization preserves the Gaussian factor-model law (Wu and
Estabrook (2016), Section 3.1, (2)): transformed parameters index the same
multivariate normal distribution. -/
public theorem multivariateGaussian_factorModel_transform {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (Λ : Matrix ι κ ℝ) (ν : ι → ℝ) (a : κ → ℝ)
    (Φ : Matrix κ κ ℝ) (Θ : Matrix ι ι ℝ)
    (U : Matrix κ κ ℝ) (β : κ → ℝ)
    (hU : IsUnit U.det) :
    ProbabilityTheory.multivariateGaussian
        ((WithLp.equiv 2 _).symm (factorModelMean ν Λ a))
        (factorModelCov Λ Φ Θ)
      = ProbabilityTheory.multivariateGaussian
        ((WithLp.equiv 2 _).symm
          (factorModelMean (ν + Λ *ᵥ β) (Λ * U) (U⁻¹ *ᵥ (a - β))))
        (factorModelCov (Λ * U) (U⁻¹ * Φ * U⁻¹ᵀ) Θ) := by
  rw [factorModelMean_transform Λ ν a U β hU,
    factorModelCov_transform Λ Φ Θ U hU]

/-- Common loadings and intercepts identify the affine transform (Wu and
Estabrook (2016), Section 2.2, strong invariance): with injective
`Λ.mulVec`, equal `Λ * U` and `ν + Λ *ᵥ β` force equal `U` and `β`. -/
public theorem transform_eq_of_common {ι κ : Type*} [Fintype κ]
    [DecidableEq κ] {Λ : Matrix ι κ ℝ} {ν : ι → ℝ}
    {U₁ U₂ : Matrix κ κ ℝ} {β₁ β₂ : κ → ℝ}
    (hΛ : Function.Injective Λ.mulVec)
    (_hU₁ : IsUnit U₁.det) (_hU₂ : IsUnit U₂.det)
    (hU : Λ * U₁ = Λ * U₂)
    (hβ : ν + Λ *ᵥ β₁ = ν + Λ *ᵥ β₂) :
    U₁ = U₂ ∧ β₁ = β₂ := by
  have hUeq : U₁ = U₂ := by
    have hcol : ∀ j, (fun k => U₁ k j) = (fun k => U₂ k j) := by
      intro j
      apply hΛ
      funext i
      have hij := congrFun (congrFun hU i) j
      simp only [Matrix.mul_apply, Matrix.mulVec] at hij ⊢
      exact hij
    ext k j
    exact congrFun (hcol j) k
  have hβeq : β₁ = β₂ := hΛ (add_left_cancel hβ)
  exact ⟨hUeq, hβeq⟩

/-- Under common loadings and intercepts, transformed factor means agree iff
original means agree (Wu and Estabrook (2016), Section 2.2): latent
comparisons need invariance. -/
public theorem transformedMeans_agree_iff_of_common {ι κ : Type*}
    [Fintype κ] [DecidableEq κ] (Λ : Matrix ι κ ℝ) (ν : ι → ℝ)
    (a₁ a₂ β₁ β₂ : κ → ℝ) (U₁ U₂ : Matrix κ κ ℝ)
    (hΛ : Function.Injective Λ.mulVec)
    (hU₁ : IsUnit U₁.det) (_hU₂ : IsUnit U₂.det)
    (hU : Λ * U₁ = Λ * U₂)
    (hβ : ν + Λ *ᵥ β₁ = ν + Λ *ᵥ β₂) :
    U₁⁻¹ *ᵥ (a₁ - β₁) = U₂⁻¹ *ᵥ (a₂ - β₂) ↔ a₁ = a₂ := by
  obtain ⟨rfl, rfl⟩ := transform_eq_of_common hΛ hU₁ _hU₂ hU hβ
  have hInvDet : IsUnit U₁⁻¹.det := Matrix.isUnit_nonsing_inv_det _ hU₁
  have hInvUnit : IsUnit U₁⁻¹ := (Matrix.isUnit_iff_isUnit_det _).mpr hInvDet
  have hInvInj : Function.Injective U₁⁻¹.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hInvUnit
  constructor
  · intro h
    have hsub : a₁ - β₁ = a₂ - β₁ := hInvInj h
    have h2 := congrArg (fun x => x + β₁) hsub
    rwa [sub_add_cancel, sub_add_cancel] at h2
  · intro h
    rw [h]

/-- Two-group affine indeterminacy, joint form (Wu and Estabrook (2016),
Section 3.1): parameterization `A` has equal factor means across the two
groups, while parameterization `B` applies independent group-specific affine
transforms `U g`, `β g` to loadings, intercepts, factor means and covariances.
Both per-group observed Gaussian laws agree, yet the factor means are equal in
`A` and unequal in `B`; proved via per-group instantiation of the universal
single-group theorem `multivariateGaussian_factorModel_transform`. -/
public theorem twoGroup_affine_indeterminacy {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (Λ : Matrix ι κ ℝ) (ν : ι → ℝ) (a : Fin 2 → (κ → ℝ))
    (Φ : Matrix κ κ ℝ) (Θ : Matrix ι ι ℝ)
    (U : Fin 2 → Matrix κ κ ℝ) (β : Fin 2 → (κ → ℝ))
    (hU : ∀ g, IsUnit (U g).det)
    (hEq : a 0 = a 1)
    (hNe : (U 0)⁻¹ *ᵥ (a 0 - β 0) ≠ (U 1)⁻¹ *ᵥ (a 1 - β 1)) :
    (∀ g, ProbabilityTheory.multivariateGaussian
        ((WithLp.equiv 2 _).symm (factorModelMean ν Λ (a g)))
        (factorModelCov Λ Φ Θ)
      = ProbabilityTheory.multivariateGaussian
        ((WithLp.equiv 2 _).symm
          (factorModelMean (ν + Λ *ᵥ β g) (Λ * U g)
            ((U g)⁻¹ *ᵥ (a g - β g))))
        (factorModelCov (Λ * U g) ((U g)⁻¹ * Φ * (U g)⁻¹ᵀ) Θ))
    ∧ a 0 = a 1
    ∧ (U 0)⁻¹ *ᵥ (a 0 - β 0) ≠ (U 1)⁻¹ *ᵥ (a 1 - β 1) := by
  refine ⟨fun g => multivariateGaussian_factorModel_transform Λ ν (a g) Φ Θ
    (U g) (β g) (hU g), hEq, hNe⟩

end

end MathlibExt.Probability.Statistics.Measurement
