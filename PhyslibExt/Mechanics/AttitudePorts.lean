/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import MathlibExt.Analysis.QuaternionRotation
public import Physlib.Mathematics.Modules.CrossProductMatrix
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Attitude ports: quaternion and matrix angular-velocity correspondence

## i. Overview

An attitude is a unit quaternion `q`; its rotation matrix is `R = rotMatrix q`, the matrix of the
action `v ↦ q v q⋆` on pure quaternions in the basis `i, j, k` (`QuaternionRotation.rotMatrix`).
With the body angular velocity `ω_B`, the quaternion kinematics are `q' = (1/2) q (0, ω_B)`, the
body vector multiplied on the right. Differentiating the action along this equation gives
`R' = R [ω_B]ₓ`, with `[ω]ₓ` Physlib's hat matrix, `[ω]ₓ v = ω ⨯₃ v`. This is the convention of
Physlib's rigid-body angular velocity: `R' = R Ω_body` with `Ω_body = [ω_B]ₓ`, and `ω_B` is
recovered as the vee of `Rᵀ R'`.

The kinematic equation keeps the quaternion norm, so a unit initial state stays unit for all
time; the equation alone, without this invariant, does not need `|q| = 1` for `R' = R [ω_B]ₓ`.
Multiplying on the left instead, `q' = (1/2) (0, ω) q`, gives `R' = [ω]ₓ R`: `ω` is then the
angular velocity in inertial components, a different frame convention, and the two products
differ in general.

Matrix-valued derivatives use Mathlib's default topology on matrices, the product topology; no
matrix norm is chosen.

Model inputs: the quaternion product order and the body-frame reading of `ω_B` are fixed as
above; time is a real parameter. Non-goals: discrete integration or renormalization schemes
(not exact continuous kinematics), Euler-angle charts, dynamics and torques.

## ii. Key results

- `Mechanics.AttitudePorts.hasDerivAt_rotMatrix_mulVec`: the derivative of the action,
  `(R v)' = R (ω_B ⨯₃ v)`.
- `Mechanics.AttitudePorts.hasDerivAt_rotMatrix`: `R' = R [ω_B]ₓ`.
- `Mechanics.AttitudePorts.crossProductVee_transpose_mul_deriv_rotMatrix`: for a unit state, the
  vee of `Rᵀ R'` is `ω_B`.
- `Mechanics.AttitudePorts.norm_eq_one_of_hasDerivAt`: the kinematics keep a unit quaternion
  unit.
- `Mechanics.AttitudePorts.hasDerivAt_rotMatrix_of_left`: the left product gives `R' = [ω]ₓ R`.

## iii. Table of contents

- A. Body-rate quaternion kinematics and the rotation matrix
  - A.1. Private helpers
  - A.2. The derivative of the rotation matrix
- B. Norm preservation
- C. The other multiplication order

## iv. References

- J. Diebel, *Representing Attitude: Euler Angles, Unit Quaternions, and Rotation Vectors*,
  2006: quaternion kinematics and their product conventions.
- F. L. Markley and J. L. Crassidis, *Fundamentals of Spacecraft Attitude Determination and
  Control*, 2014, ch. 3: attitude kinematics.
- L. D. Landau and E. M. Lifshitz, *Mechanics*, Section 35 (angular velocity in body axes).
- Mathlib's quaternions, `MathlibExt.Analysis.QuaternionRotation`, and Physlib's hat and vee maps
  (`Physlib.Mathematics.Modules.CrossProductMatrix`) and rigid-body angular velocity.
-/

@[expose] public section

open Quaternion
open scoped Matrix

namespace Mechanics.AttitudePorts

open QuaternionRotation Matrix

/-! ## A. Body-rate quaternion kinematics and the rotation matrix -/

/-- The pure quaternion `(0, u) = u₀ i + u₁ j + u₂ k` with imaginary coordinates `u`. -/
def pureQuat (u : Fin 3 → ℝ) : ℍ := ⟨0, u 0, u 1, u 2⟩

/-! ### A.1. Private helpers -/

/-- The imaginary coordinates of a quaternion as a continuous real-linear map. -/
private noncomputable def imCoordsCLM : ℍ →L[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => imCoords x
      map_add' := fun x y => by ext i; fin_cases i <;> simp [imCoords]
      map_smul' := fun c x => by ext i; fin_cases i <;> simp [imCoords] }

/-- Quaternion conjugation as a continuous real-linear map. -/
private noncomputable def starCLM : ℍ →L[ℝ] ℍ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => star x
      map_add' := fun x y => star_add x y
      map_smul' := fun c x => by ext <;> simp }

/-- The conjugate of a quaternion curve has the conjugate derivative. -/
private lemma hasDerivAt_star' {q : ℝ → ℍ} {q' : ℍ} {t : ℝ} (hq : HasDerivAt q q' t) :
    HasDerivAt (fun s => star (q s)) (star q') t :=
  starCLM.hasFDerivAt.comp_hasDerivAt t hq

/-- `R v` is the imaginary part of the conjugate `q (0, v) q⋆`, for every quaternion `q`. -/
private lemma rotMatrix_mulVec_eq (q : ℍ) (v : Fin 3 → ℝ) :
    rotMatrix q *ᵥ v = imCoords (q * pureQuat v * star q) := by
  ext a
  fin_cases a <;>
    simp [rotMatrix, imCoords, imBasis, pureQuat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring

/-- Along `q' = (1/2) q (0, w)`, the derivative of `q (0, v) q⋆` is `q (0, w ⨯₃ v) q⋆`. -/
private lemma conj_deriv_identity (q : ℍ) (w v : Fin 3 → ℝ) :
    (1 / 2 : ℝ) • (q * pureQuat w) * pureQuat v * star q +
        q * pureQuat v * star ((1 / 2 : ℝ) • (q * pureQuat w)) =
      q * pureQuat (w ⨯₃ v) * star q := by
  ext <;> simp [pureQuat, cross_apply] <;> ring

/-- Along `q' = (1/2) (0, w) q`, the derivative of `q (0, v) q⋆` is `(0, w ⨯₃ u)`, with `u`
the imaginary coordinates of `q (0, v) q⋆`. -/
private lemma conj_deriv_identity_left (q : ℍ) (w v : Fin 3 → ℝ) :
    (1 / 2 : ℝ) • (pureQuat w * q) * pureQuat v * star q +
        q * pureQuat v * star ((1 / 2 : ℝ) • (pureQuat w * q)) =
      pureQuat (w ⨯₃ imCoords (q * pureQuat v * star q)) := by
  ext <;> simp [pureQuat, imCoords, cross_apply] <;> ring

/-- A matrix applied to the basis vector `e_j` is its column `j`. -/
private lemma mulVec_single (A : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    (A *ᵥ Pi.single j 1) i = A i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- A matrix-valued curve has derivative `A` when each column has the matching column of `A`
as derivative. -/
private lemma hasDerivAt_matrix_of_mulVec {f : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {A : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (h : ∀ j : Fin 3, HasDerivAt (fun s => f s *ᵥ Pi.single j 1) (A *ᵥ Pi.single j 1) t) :
    HasDerivAt f A t := by
  have h' : HasDerivAt (fun s => (f s : Fin 3 → Fin 3 → ℝ)) (A : Fin 3 → Fin 3 → ℝ) t := by
    refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
    have hj := hasDerivAt_pi.mp (h j) i
    simp only [mulVec_single] at hj
    exact hj
  exact h'

/-- `Rᵀ R = |q|⁴ 1` for every quaternion `q`. -/
private lemma rotMatrix_transpose_mul_self' (q : ℍ) :
    (rotMatrix q)ᵀ * rotMatrix q = (normSq q) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotMatrix, imCoords, imBasis, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_three, Quaternion.normSq_def'] <;>
    ring

/-! ### A.2. The derivative of the rotation matrix -/

/-- Derivative of the action along the body-rate kinematics: if `q' = (1/2) q (0, ω_B)` at `t`,
then for every vector `v`, `(R v)' = R (ω_B ⨯₃ v)` with `R = rotMatrix q`. This is the form
`R' v = R (ω_B × v)` of Physlib's rigid-body angular velocity. -/
lemma hasDerivAt_rotMatrix_mulVec {q : ℝ → ℍ} {ω : ℝ → Fin 3 → ℝ} {t : ℝ}
    (hq : HasDerivAt q ((1 / 2 : ℝ) • (q t * pureQuat (ω t))) t) (v : Fin 3 → ℝ) :
    HasDerivAt (fun s => rotMatrix (q s) *ᵥ v) (rotMatrix (q t) *ᵥ (ω t ⨯₃ v)) t := by
  have hprod : HasDerivAt (fun s => q s * pureQuat v * star (q s))
      ((1 / 2 : ℝ) • (q t * pureQuat (ω t)) * pureQuat v * star (q t) +
        q t * pureQuat v * star ((1 / 2 : ℝ) • (q t * pureQuat (ω t)))) t :=
    (hq.mul_const (pureQuat v)).fun_mul (hasDerivAt_star' hq)
  rw [conj_deriv_identity] at hprod
  have hcomp := imCoordsCLM.hasFDerivAt.comp_hasDerivAt t hprod
  have hfun : (fun s => rotMatrix (q s) *ᵥ v) =
      imCoordsCLM ∘ fun s => q s * pureQuat v * star (q s) := by
    funext s
    rw [rotMatrix_mulVec_eq]
    rfl
  rw [hfun, rotMatrix_mulVec_eq]
  exact hcomp

/-- The matrix kinematics: if `q' = (1/2) q (0, ω_B)` at `t`, then `R' = R [ω_B]ₓ` at `t` for
`R = rotMatrix q`, with the default topology on matrices. No unit-norm hypothesis is needed. -/
lemma hasDerivAt_rotMatrix {q : ℝ → ℍ} {ω : ℝ → Fin 3 → ℝ} {t : ℝ}
    (hq : HasDerivAt q ((1 / 2 : ℝ) • (q t * pureQuat (ω t))) t) :
    HasDerivAt (fun s => rotMatrix (q s)) (rotMatrix (q t) * crossProductMatrix (ω t)) t := by
  apply hasDerivAt_matrix_of_mulVec
  intro j
  rw [← Matrix.mulVec_mulVec]
  have h := hasDerivAt_rotMatrix_mulVec hq (Pi.single j 1)
  convert h using 2
  ext i
  fin_cases i <;> fin_cases j <;>
    simp [crossProductMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cross_apply]

/-- Matching Physlib's body angular velocity, the vee of `Rᵀ R'`: for a unit state `|q(t)| = 1`
obeying `q' = (1/2) q (0, ω_B)` at `t`, the vee of `R(t)ᵀ R'(t)` is `ω_B(t)`. -/
lemma crossProductVee_transpose_mul_deriv_rotMatrix {q : ℝ → ℍ} {ω : ℝ → Fin 3 → ℝ} {t : ℝ}
    (hq : HasDerivAt q ((1 / 2 : ℝ) • (q t * pureQuat (ω t))) t) (hunit : ‖q t‖ = 1) :
    crossProductVee ((rotMatrix (q t))ᵀ * deriv (fun s => rotMatrix (q s)) t) = ω t := by
  have hN : normSq (q t) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hunit, mul_one]
  have hd : deriv (fun s => rotMatrix (q s)) t = rotMatrix (q t) * crossProductMatrix (ω t) := by
    exact HasDerivAt.deriv (F := Fin 3 → Fin 3 → ℝ) (hasDerivAt_rotMatrix hq)
  rw [hd, ← Matrix.mul_assoc, rotMatrix_transpose_mul_self', hN, one_pow, one_smul,
    Matrix.one_mul]
  ext i
  fin_cases i <;> simp [crossProductVee, crossProductMatrix]

/-! ## B. Norm preservation -/

/-- The body-rate kinematics keep the quaternion norm: if `q' = (1/2) q (0, ω_B)` at every time
and `|q(0)| = 1`, then `|q(t)| = 1` for every `t`. -/
lemma norm_eq_one_of_hasDerivAt {q : ℝ → ℍ} {ω : ℝ → Fin 3 → ℝ}
    (hq : ∀ t, HasDerivAt q ((1 / 2 : ℝ) • (q t * pureQuat (ω t))) t) (h₀ : ‖q 0‖ = 1) (t : ℝ) :
    ‖q t‖ = 1 := by
  have hderiv : ∀ s, HasDerivAt (fun s => ‖q s‖ ^ 2) 0 s := by
    intro s
    have h := (hq s).norm_sq
    convert h using 1
    rw [real_inner_smul_right, Quaternion.inner_def]
    simp [pureQuat]
    ring
  have hconst := is_const_of_deriv_eq_zero (f := fun s => ‖q s‖ ^ 2)
    (fun s => (hderiv s).differentiableAt) (fun s => (hderiv s).deriv)
  have h1 : ‖q t‖ ^ 2 = 1 := by
    have := hconst t 0
    simp only [h₀, one_pow] at this
    exact this
  have hn := norm_nonneg (q t)
  nlinarith

/-! ## C. The other multiplication order -/

/-- Left multiplication is a different frame convention: if `q' = (1/2) (0, ω) q` at `t`, then
`R' = [ω]ₓ R`, so `ω` is the angular velocity in inertial components (`R' Rᵀ = [ω]ₓ` for a unit
state). -/
lemma hasDerivAt_rotMatrix_of_left {q : ℝ → ℍ} {ω : ℝ → Fin 3 → ℝ} {t : ℝ}
    (hq : HasDerivAt q ((1 / 2 : ℝ) • (pureQuat (ω t) * q t)) t) :
    HasDerivAt (fun s => rotMatrix (q s)) (crossProductMatrix (ω t) * rotMatrix (q t)) t := by
  apply hasDerivAt_matrix_of_mulVec
  intro j
  have hprod : HasDerivAt (fun s => q s * pureQuat (Pi.single j 1) * star (q s))
      ((1 / 2 : ℝ) • (pureQuat (ω t) * q t) * pureQuat (Pi.single j 1) * star (q t) +
        q t * pureQuat (Pi.single j 1) * star ((1 / 2 : ℝ) • (pureQuat (ω t) * q t))) t :=
    (hq.mul_const (pureQuat (Pi.single j 1))).fun_mul (hasDerivAt_star' hq)
  rw [conj_deriv_identity_left] at hprod
  have hcomp := imCoordsCLM.hasFDerivAt.comp_hasDerivAt t hprod
  have hfun : (fun s => rotMatrix (q s) *ᵥ Pi.single j 1) =
      imCoordsCLM ∘ fun s => q s * pureQuat (Pi.single j 1) * star (q s) := by
    funext s
    rw [rotMatrix_mulVec_eq]
    rfl
  rw [hfun, ← Matrix.mulVec_mulVec, rotMatrix_mulVec_eq]
  convert hcomp using 1
  ext i
  fin_cases i <;>
    simp [imCoordsCLM, crossProductMatrix, imCoords, pureQuat, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, cross_apply] <;>
    ring

end Mechanics.AttitudePorts
