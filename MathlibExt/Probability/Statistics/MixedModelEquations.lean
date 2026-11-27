/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GeneralizedLeastSquares
import Mathlib.Algebra.Order.Star.Real

/-!
# Henderson’s mixed-model equations

For a linear mixed model with marginal covariance `Z G Zᵀ + R`, Henderson's
equations yield the generalized least-squares estimate of the fixed effects.
-/

@[expose] public section

open Matrix
open MathlibExt.Probability.Statistics.GeneralizedLeastSquares

namespace MathlibExt.Biology.StatisticalGenetics.MixedModel

section MME

variable {n p q : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
  [Fintype q] [DecidableEq q]

/-- The phenotypic covariance `V = Z G Zᵀ + R` of the linear mixed model
`y = X b + Z u + e` with `Cov u = G`, `Cov e = R`. -/
def phenCov (Z : Matrix n q ℝ) (G : Matrix q q ℝ) (R : Matrix n n ℝ) : Matrix n n ℝ :=
  Z * G * Zᵀ + R

/-- Henderson's mixed-model equations for `y = X b + Z u + e`, `Cov u = G`, `Cov e = R`:
`[Xᵀ R⁻¹ X, Xᵀ R⁻¹ Z; Zᵀ R⁻¹ X, Zᵀ R⁻¹ Z + G⁻¹] [b; u] = [Xᵀ R⁻¹ y; Zᵀ R⁻¹ y]`. -/
def IsMMESolution (X : Matrix n p ℝ) (Z : Matrix n q ℝ) (G : Matrix q q ℝ) (R : Matrix n n ℝ)
    (y : n → ℝ) (b : p → ℝ) (u : q → ℝ) : Prop :=
  (Xᵀ * R⁻¹ * X) *ᵥ b + (Xᵀ * R⁻¹ * Z) *ᵥ u = (Xᵀ * R⁻¹) *ᵥ y ∧
    (Zᵀ * R⁻¹ * X) *ᵥ b + (Zᵀ * R⁻¹ * Z + G⁻¹) *ᵥ u = (Zᵀ * R⁻¹) *ᵥ y

variable {X : Matrix n p ℝ} {Z : Matrix n q ℝ} {G : Matrix q q ℝ} {R : Matrix n n ℝ}

omit [Fintype n] [DecidableEq n] [DecidableEq q] in
/-- `V = Z G Zᵀ + R` is positive definite. -/
theorem posDef_phenCov [Finite n] (hG : G.PosDef) (hR : R.PosDef) : (phenCov Z G R).PosDef := by
  have h := hG.posSemidef.mul_mul_conjTranspose_same Z
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact Matrix.PosDef.posSemidef_add h hR

private theorem posDef_mmeBlock (hG : G.PosDef) (hR : R.PosDef) :
    (Zᵀ * R⁻¹ * Z + G⁻¹).PosDef := by
  have h := hR.inv.posSemidef.conjTranspose_mul_mul_same Z
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact Matrix.PosDef.posSemidef_add h hG.inv

private theorem isUnit_det_of_posDef {k : Type*} [Fintype k] [DecidableEq k] {A : Matrix k k ℝ}
    (hA : A.PosDef) : IsUnit A.det :=
  (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit

/-- The key identity behind the mixed-model equations:
`(Zᵀ R⁻¹ Z + G⁻¹) G Zᵀ V⁻¹ = Zᵀ R⁻¹`. -/
private theorem mmeBlock_mul (hG : G.PosDef) (hR : R.PosDef) :
    (Zᵀ * R⁻¹ * Z + G⁻¹) * (G * Zᵀ * (phenCov Z G R)⁻¹) = Zᵀ * R⁻¹ := by
  have hV := isUnit_det_of_posDef (posDef_phenCov (Z := Z) hG hR)
  have h1 : (Zᵀ * R⁻¹ * Z + G⁻¹) * (G * Zᵀ) = Zᵀ * R⁻¹ * phenCov Z G R := by
    rw [phenCov, Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc G⁻¹ G,
      Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hG), Matrix.one_mul,
      Matrix.mul_assoc Zᵀ R⁻¹ R, Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hR),
      Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hV, Matrix.mul_one]

omit [DecidableEq q] in
/-- The second identity: `R⁻¹ - R⁻¹ Z G Zᵀ V⁻¹ = V⁻¹`. -/
private theorem inv_sub_eq (hG : G.PosDef) (hR : R.PosDef) :
    R⁻¹ - R⁻¹ * Z * (G * Zᵀ * (phenCov Z G R)⁻¹) = (phenCov Z G R)⁻¹ := by
  have hV := isUnit_det_of_posDef (posDef_phenCov (Z := Z) hG hR)
  have h : R⁻¹ * phenCov Z G R - R⁻¹ * Z * (G * Zᵀ) = 1 := by
    rw [phenCov, Matrix.mul_add, Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hR)]
    simp only [Matrix.mul_assoc]
    abel
  calc R⁻¹ - R⁻¹ * Z * (G * Zᵀ * (phenCov Z G R)⁻¹)
      = (R⁻¹ * phenCov Z G R - R⁻¹ * Z * (G * Zᵀ)) * (phenCov Z G R)⁻¹ := by
        rw [Matrix.sub_mul, Matrix.mul_assoc R⁻¹ (phenCov Z G R), Matrix.mul_nonsing_inv _ hV,
          Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = (phenCov Z G R)⁻¹ := by rw [h, Matrix.one_mul]

private theorem aux_sub_add_iff {M : Type*} [AddCommGroup M] (a b c : M) :
    a - b + c = a ↔ b - c = 0 := by
  rw [← sub_eq_zero (a := a - b + c), show a - b + c - a = c - b by abel, sub_eq_zero,
    sub_eq_zero, eq_comm]

omit [DecidableEq p] in
/-- **Henderson's mixed-model equations** (Henderson 1975; Robinson 1991): for positive definite
`G` and `R` and `V = Z G Zᵀ + R`, `(b, u)` solves the mixed-model equations if and only if `b`
solves the generalized least-squares normal equations `Xᵀ V⁻¹ X b = Xᵀ V⁻¹ y` and
`u = G Zᵀ V⁻¹ (y - X b)`. -/
theorem isMMESolution_iff (hG : G.PosDef) (hR : R.PosDef) (y : n → ℝ) (b : p → ℝ)
    (u : q → ℝ) :
    IsMMESolution X Z G R y b u ↔
      (Xᵀ * (phenCov Z G R)⁻¹ * X) *ᵥ b = (Xᵀ * (phenCov Z G R)⁻¹) *ᵥ y ∧
        u = (G * Zᵀ * (phenCov Z G R)⁻¹) *ᵥ (y - X *ᵥ b) := by
  set V := phenCov Z G R with hVdef
  set C := Zᵀ * R⁻¹ * Z + G⁻¹ with hC
  set K := G * Zᵀ * V⁻¹ with hK
  have hCd := isUnit_det_of_posDef (posDef_mmeBlock (Z := Z) hG hR)
  have hCK : C * K = Zᵀ * R⁻¹ := mmeBlock_mul hG hR
  have hRK : R⁻¹ - R⁻¹ * Z * K = V⁻¹ := inv_sub_eq hG hR
  -- the second equation is equivalent to `u = K (y - X b)`
  have h2 : (Zᵀ * R⁻¹ * X) *ᵥ b + C *ᵥ u = (Zᵀ * R⁻¹) *ᵥ y ↔ u = K *ᵥ (y - X *ᵥ b) := by
    have e : (Zᵀ * R⁻¹ * X) *ᵥ b + C *ᵥ u = (Zᵀ * R⁻¹) *ᵥ y ↔
        C *ᵥ u = (Zᵀ * R⁻¹) *ᵥ (y - X *ᵥ b) := by
      rw [mulVec_sub, mulVec_mulVec, eq_sub_iff_add_eq, add_comm]
    rw [e, ← hCK, ← mulVec_mulVec]
    constructor
    · intro h
      have := congrArg (C⁻¹ *ᵥ ·) h
      simp only [mulVec_mulVec, ← Matrix.mul_assoc] at this
      rwa [Matrix.nonsing_inv_mul _ hCd, Matrix.one_mul, one_mulVec] at this
    · intro h; rw [h]
  -- given `u = K (y - X b)`, the first equation is the GLS normal equation
  have h1 : ∀ u, u = K *ᵥ (y - X *ᵥ b) →
      ((Xᵀ * R⁻¹ * X) *ᵥ b + (Xᵀ * R⁻¹ * Z) *ᵥ u = (Xᵀ * R⁻¹) *ᵥ y ↔
        (Xᵀ * V⁻¹ * X) *ᵥ b = (Xᵀ * V⁻¹) *ᵥ y) := by
    intro u hu
    subst hu
    have hw : (Xᵀ * R⁻¹ * X) *ᵥ b =
        (Xᵀ * R⁻¹) *ᵥ y - (Xᵀ * R⁻¹) *ᵥ (y - X *ᵥ b) := by
      rw [mulVec_sub, mulVec_mulVec]; abel
    have hv : (Xᵀ * V⁻¹) *ᵥ (y - X *ᵥ b) = (Xᵀ * R⁻¹) *ᵥ (y - X *ᵥ b) -
        (Xᵀ * R⁻¹ * Z) *ᵥ (K *ᵥ (y - X *ᵥ b)) := by
      rw [← hRK, mulVec_mulVec, ← sub_mulVec]
      congr 1
      simp only [Matrix.mul_sub, Matrix.mul_assoc]
    have e1 : (Xᵀ * R⁻¹ * X) *ᵥ b + (Xᵀ * R⁻¹ * Z) *ᵥ (K *ᵥ (y - X *ᵥ b)) =
        (Xᵀ * R⁻¹) *ᵥ y ↔ (Xᵀ * V⁻¹) *ᵥ (y - X *ᵥ b) = 0 := by
      rw [hw, hv, aux_sub_add_iff]
    rw [e1, mulVec_sub, mulVec_mulVec, sub_eq_zero, eq_comm]
  constructor
  · rintro ⟨e1, e2⟩
    have hu := h2.mp e2
    exact ⟨(h1 u hu).mp e1, hu⟩
  · rintro ⟨e1, hu⟩
    exact ⟨(h1 u hu).mpr e1, h2.mpr hu⟩

/-- **The MME solution is the GLS estimate and the BLUP** (Henderson 1975): if moreover
`Xᵀ V⁻¹ X` is invertible, the mixed-model equations have the unique solution
`b̂ = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹ y` (the GLS estimate) and `û = G Zᵀ V⁻¹ (y - X b̂)`. -/
theorem isMMESolution_iff_gls (hG : G.PosDef) (hR : R.PosDef)
    (hX : IsUnit (Xᵀ * (phenCov Z G R)⁻¹ * X)) (y : n → ℝ) (b : p → ℝ) (u : q → ℝ) :
    IsMMESolution X Z G R y b u ↔
      b = glsMatrix X (phenCov Z G R) *ᵥ y ∧
        u = (G * Zᵀ * (phenCov Z G R)⁻¹) *ᵥ (y - X *ᵥ b) := by
  rw [isMMESolution_iff hG hR]
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hX
  refine and_congr_left fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · rw [glsMatrix, Matrix.mul_assoc _ Xᵀ, ← mulVec_mulVec, ← h, mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hd, one_mulVec]
  · rw [h, glsMatrix, mulVec_mulVec]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]

end MME

end MathlibExt.Biology.StatisticalGenetics.MixedModel
