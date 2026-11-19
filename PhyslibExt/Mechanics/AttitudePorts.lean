/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.Analysis.QuaternionRotation
public import Physlib.Mathematics.Modules.CrossProductMatrix
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Attitude ports: quaternion angular-velocity correspondence and reaction-wheel momentum

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

A reaction wheel exchanges angular momentum with the body about a fixed axis, a principal axis
common to body and wheel, on which the gyroscopic term of Euler's equations vanishes. With `J_b`
the axial inertia of the body without the wheel, `I_w` that of the wheel, the body rate `ω`, the
wheel's spin rate `Ω` relative to the body, the motor torque `T_m` on the wheel (its reaction
`-T_m` acts on the body) and the external torque `τ_ext`, the body obeys `J_b ω' = τ_ext - T_m`
and the wheel `I_w (ω' + Ω') = T_m`. The locked inertia `J = J_b + I_w > 0`, the wheel's momentum
`h = I_w Ω` relative to the body and the commanded momentum rate `u = h'` turn these exactly into
the reduced model `J ω' = τ_ext - u`, `h' = u`, and `J ω + h = J_b ω + I_w (ω + Ω)` is the total
angular momentum about the axis. The motor torque is `T_m = u + I_w ω'`: it equals `u` while the
body rate is constant, so a motor-torque limit bounds `u` only up to `I_w |ω'|`. The total
momentum has rate `τ_ext`, so without external torque it is conserved whatever the command, and
the body rate changes by `-(h(t) - h(0)) / J`. The limits `|u| ≤ umax` on the commanded rate and
`|h| ≤ hmax` on the relative momentum, a wheel-speed limit, over a horizon `[0, T]` with `T ≥ 0`
become a condition on the command alone, `|h(0) + ∫₀ᵗ u| ≤ hmax`, which every command with
`|u| ≤ umax` meets once `|h(0)| + umax T ≤ hmax`. A constant command `c` drives
`h(t) = h(0) + c t`; for `c ≠ 0` it reaches the momentum limit at a finite time and is
inadmissible on every longer horizon, whatever the command limit.

Model inputs: the quaternion product order and the body-frame reading of `ω_B` are fixed as
above; time is a real parameter; the wheel model is the scalar fixed-axis model above, with axial
components in one consistent unit system. Non-goals: discrete integration or renormalization
schemes (not exact continuous kinematics), Euler-angle charts, three-axis attitude dynamics,
multibody rotor dynamics, friction and motor models, and momentum management or desaturation
laws.

## ii. Key results

- `Mechanics.AttitudePorts.hasDerivAt_rotMatrix_mulVec`: the derivative of the action,
  `(R v)' = R (ω_B ⨯₃ v)`.
- `Mechanics.AttitudePorts.hasDerivAt_rotMatrix`: `R' = R [ω_B]ₓ`.
- `Mechanics.AttitudePorts.crossProductVee_transpose_mul_deriv_rotMatrix`: for a unit state, the
  vee of `Rᵀ R'` is `ω_B`.
- `Mechanics.AttitudePorts.norm_eq_one_of_hasDerivAt`: the kinematics keep a unit quaternion
  unit.
- `Mechanics.AttitudePorts.hasDerivAt_rotMatrix_of_left`: the left product gives `R' = [ω]ₓ R`.
- `Mechanics.AttitudePorts.hasDerivAt_wheel_totalMomentum`,
  `Mechanics.AttitudePorts.wheel_momentum_exchange`: the total momentum `J ω + h` has rate
  `τ_ext`, and without external torque the wheel and the body exchange momentum.
- `Mechanics.AttitudePorts.WheelAdmissible`, `Mechanics.AttitudePorts.wheelAdmissible_iff_integral`,
  `Mechanics.AttitudePorts.wheelAdmissible_of_reserve`: actuator admissibility on a horizon, as a
  condition on the command and from a momentum reserve.
- `Mechanics.AttitudePorts.constCommand_admissible_iff`,
  `Mechanics.AttitudePorts.constCommand_momentum_limit`: a constant command is admissible exactly
  when its endpoint momenta are, and a nonzero one reaches the momentum limit at a finite time.

## iii. Table of contents

- A. Body-rate quaternion kinematics and the rotation matrix
  - A.1. Private helpers
  - A.2. The derivative of the rotation matrix
- B. Norm preservation
- C. The other multiplication order
- D. Fixed-axis reaction wheel

## iv. References

- J. Diebel, *Representing Attitude: Euler Angles, Unit Quaternions, and Rotation Vectors*,
  2006: quaternion kinematics and their product conventions.
- F. L. Markley and J. L. Crassidis, *Fundamentals of Spacecraft Attitude Determination and
  Control*, 2014, ch. 3: attitude kinematics.
- L. D. Landau and E. M. Lifshitz, *Mechanics*, Section 35 (angular velocity in body axes).
- B. Wie, *Space Vehicle Dynamics and Control*, 2nd edition, 2008 (reaction wheels;
  momentum-exchange actuators and wheel momentum saturation).
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

/-- `R v` is the imaginary part of the conjugate `q (0, v) q⋆`, for every quaternion `q`:
`QuaternionRotation.rotMatrix_mulVec` at the pure quaternion `(0, v)`. -/
private lemma rotMatrix_mulVec_eq (q : ℍ) (v : Fin 3 → ℝ) :
    rotMatrix q *ᵥ v = imCoords (q * pureQuat v * star q) := by
  have hv : pureQuat v ∈ pureIm := by simp [pureIm, pureQuat]
  have hc : imCoords (pureQuat v) = v := by
    ext i
    fin_cases i <;> simp [imCoords, pureQuat]
  have h := rotMatrix_mulVec (q := q) hv
  rwa [hc] at h

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
  rw [hd, ← Matrix.mul_assoc, rotMatrix_transpose_mul_self, hN, one_pow, one_smul,
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

open Set

/-! ## D. Fixed-axis reaction wheel -/

/-- A wheel command `u` with wheel momentum `h` is admissible on the horizon `[0, T]` for the
command limit `umax` and the momentum limit `hmax`: the horizon is a duration, `0 ≤ T`, and
`|u t| ≤ umax` and `|h t| ≤ hmax` at every `t ∈ [0, T]`. In the reduced model `h` is the wheel's
momentum relative to the body, so `hmax` is a wheel-speed limit, and `u = h'` is its commanded
rate. -/
def WheelAdmissible (umax hmax T : ℝ) (u h : ℝ → ℝ) : Prop :=
  0 ≤ T ∧ ∀ t ∈ Icc 0 T, |u t| ≤ umax ∧ |h t| ≤ hmax

/-- Momentum exchange: if the body obeys `J ω' = τ_ext - u` and the wheel `h' = u` at `t`, the
total angular momentum `J ω + h` about the axis has derivative `τ_ext` at `t`. With `J` the axial
inertia of the body with the wheel locked and `h` the wheel's momentum relative to the body,
`J ω + h` is the exact total angular momentum, and the body equation is exact when `u` is the rate
`h'`. The identity does not use the value of `J`; the model takes `J > 0`. -/
lemma hasDerivAt_wheel_totalMomentum {J : ℝ} {ω ω' h u τ : ℝ → ℝ} {t : ℝ}
    (hω : HasDerivAt ω (ω' t) t) (hh : HasDerivAt h (u t) t) (hbody : J * ω' t = τ t - u t) :
    HasDerivAt (fun s => J * ω s + h s) (τ t) t := by
  have hsum := (hω.const_mul J).add hh
  have heq : J * ω' t + u t = τ t := by linarith
  rw [heq] at hsum
  exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => rfl)

/-- Without external torque on `[0, T]` the total momentum `J ω + h` is conserved, whatever the
command `u`, and for `J > 0` the body rate changes by `-(h t - h 0) / J`: the momentum the wheel
gains relative to the body, the locked vehicle `J ω` loses. -/
lemma wheel_momentum_exchange {J T : ℝ} (hJ : 0 < J) {ω ω' h u τ : ℝ → ℝ}
    (hω : ∀ t ∈ Icc 0 T, HasDerivAt ω (ω' t) t) (hh : ∀ t ∈ Icc 0 T, HasDerivAt h (u t) t)
    (hbody : ∀ t ∈ Icc 0 T, J * ω' t = τ t - u t) (hτ : ∀ t ∈ Icc 0 T, τ t = 0) :
    ∀ t ∈ Icc 0 T, J * ω t + h t = J * ω 0 + h 0 ∧ ω t - ω 0 = -(h t - h 0) / J := by
  have hH : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => J * ω s + h s) 0 t := by
    intro t ht
    have hsum := ((hω t ht).const_mul J).add (hh t ht)
    have heq : J * ω' t + u t = 0 := by
      have hb := hbody t ht
      have hτt := hτ t ht
      linarith
    rw [heq] at hsum
    exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => rfl)
  have hconst : ∀ t ∈ Icc 0 T, (fun s => J * ω s + h s) t = (fun s => J * ω s + h s) 0 :=
    constant_of_has_deriv_right_zero (HasDerivAt.continuousOn hH)
      (fun x hx => (hH x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
  intro t ht
  have hJne : J ≠ 0 := ne_of_gt hJ
  have hc : J * ω t + h t = J * ω 0 + h 0 := hconst t ht
  refine ⟨hc, ?_⟩
  field_simp
  linarith

/-- The momentum limit as a condition on the input: along the wheel equation `h' = u` on `[0, T]`,
with `u` integrable there, the command is admissible on `[0, T]` exactly when `0 ≤ T` and
`|u t| ≤ umax` and `|h 0 + ∫₀ᵗ u| ≤ hmax` for every `t ∈ [0, T]`. -/
lemma wheelAdmissible_iff_integral {umax hmax T : ℝ} {u h : ℝ → ℝ}
    (hh : ∀ t ∈ Icc 0 T, HasDerivAt h (u t) t)
    (hu : IntervalIntegrable u MeasureTheory.volume 0 T) :
    WheelAdmissible umax hmax T u h ↔
      0 ≤ T ∧ ∀ t ∈ Icc 0 T, |u t| ≤ umax ∧ |h 0 + ∫ s in (0 : ℝ)..t, u s| ≤ hmax := by
  have hftc : ∀ t ∈ Icc 0 T, h t = h 0 + ∫ s in (0 : ℝ)..t, u s := by
    intro t ht
    have hsub : ∫ s in (0 : ℝ)..t, u s = h t - h 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
      · rw [uIcc_of_le ht.1] at hx
        exact hh x ⟨hx.1, le_trans hx.2 ht.2⟩
      · apply hu.mono_set
        have h0T : (0 : ℝ) ≤ T := le_trans ht.1 ht.2
        rw [uIcc_of_le ht.1, uIcc_of_le h0T]
        intro x hx
        exact ⟨hx.1, le_trans hx.2 ht.2⟩
    rw [hsub]
    ring
  constructor
  · rintro ⟨hT, hadm⟩
    refine ⟨hT, fun t ht => ?_⟩
    obtain ⟨hu1, hh1⟩ := hadm t ht
    refine ⟨hu1, ?_⟩
    rw [← hftc t ht]
    exact hh1
  · rintro ⟨hT, hrhs⟩
    refine ⟨hT, fun t ht => ?_⟩
    obtain ⟨hu1, hh1⟩ := hrhs t ht
    refine ⟨hu1, ?_⟩
    rw [hftc t ht]
    exact hh1

/-- Finite-horizon reserve condition: along the wheel equation `h' = u` on `[0, T]`, `T ≥ 0`, a
command with `|u| ≤ umax` on `[0, T]` is admissible on `[0, T]` whenever `|h 0| + umax T ≤ hmax`. -/
lemma wheelAdmissible_of_reserve {umax hmax T : ℝ} {u h : ℝ → ℝ} (hT : 0 ≤ T)
    (hh : ∀ t ∈ Icc 0 T, HasDerivAt h (u t) t) (hu : ∀ t ∈ Icc 0 T, |u t| ≤ umax)
    (hres : |h 0| + umax * T ≤ hmax) : WheelAdmissible umax hmax T u h := by
  refine ⟨hT, fun t ht => ?_⟩
  have humax : 0 ≤ umax := le_trans (abs_nonneg _) (hu t ht)
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment' (f := h) (f' := u) (C := umax)
    (a := 0) (b := T)
    (fun x hx => (hh x hx).hasDerivWithinAt)
    (fun x hx => by
      have h1 := hu x (Ico_subset_Icc_self hx)
      rwa [Real.norm_eq_abs])
    t ht
  have htri : |h t - h 0| ≤ umax * t := by
    simpa [Real.norm_eq_abs] using hbound
  have h2 : umax * t ≤ umax * T := mul_le_mul_of_nonneg_left ht.2 humax
  have h1 : |h t| ≤ |h 0| + |h t - h 0| := by
    have e : h t = h 0 + (h t - h 0) := by ring
    conv_lhs => rw [e]
    exact abs_add_le (h 0) (h t - h 0)
  refine ⟨hu t ht, ?_⟩
  linarith

/-- A constant command `c` drives the affine momentum `h t = h 0 + c * t` on `[0, T]`. -/
private lemma constCommand_eq {c T : ℝ} {h : ℝ → ℝ}
    (hh : ∀ t ∈ Icc 0 T, HasDerivAt h c t) :
    ∀ t ∈ Icc 0 T, h t = h 0 + c * t := by
  have haff : ∀ x : ℝ, HasDerivAt (fun s => h 0 + c * s) c x := by
    intro x
    have h1 := (hasDerivAt_const x (h 0)).add ((hasDerivAt_id' x).const_mul c)
    have heq : (0 : ℝ) + c * 1 = c := by ring
    rw [heq] at h1
    exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)
  have heq := eq_of_has_deriv_right_eq (f := h) (g := fun s => h 0 + c * s) (f' := fun _ => c)
    (fun x hx => (hh x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (fun x hx => (haff x).hasDerivWithinAt)
    (HasDerivAt.continuousOn hh)
    (HasDerivAt.continuousOn (fun x _ => haff x))
    (show h 0 = h 0 + c * 0 by ring)
  intro t ht
  exact heq t ht

/-- A constant command `c` on `[0, T]`, `T ≥ 0`: the wheel momentum is `h 0 + c t`, and the command
is admissible on `[0, T]` exactly when `|c| ≤ umax`, `|h 0| ≤ hmax` and `|h 0 + c T| ≤ hmax`. -/
lemma constCommand_admissible_iff {umax hmax c T : ℝ} {h : ℝ → ℝ} (hT : 0 ≤ T)
    (hh : ∀ t ∈ Icc 0 T, HasDerivAt h c t) :
    WheelAdmissible umax hmax T (fun _ => c) h ↔
      |c| ≤ umax ∧ |h 0| ≤ hmax ∧ |h 0 + c * T| ≤ hmax := by
  have hform : ∀ t ∈ Icc 0 T, h t = h 0 + c * t := constCommand_eq hh
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_refl 0, hT⟩
  have hTmem : T ∈ Icc 0 T := ⟨hT, le_refl T⟩
  constructor
  · rintro ⟨-, hadm⟩
    obtain ⟨huc, hh0⟩ := hadm 0 h0mem
    obtain ⟨-, hhT⟩ := hadm T hTmem
    refine ⟨?_, hh0, ?_⟩
    · simpa using huc
    · rw [hform T hTmem] at hhT
      exact hhT
  · rintro ⟨huc, hh0, hhT⟩
    refine ⟨hT, fun t ht => ⟨?_, ?_⟩⟩
    · simpa using huc
    · rw [hform t ht]
      by_cases hTeq : T = 0
      · have ht0 : t = 0 := le_antisymm (hTeq ▸ ht.2) ht.1
        rw [ht0]
        simpa using hh0
      · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hTeq)
        have hconv : h 0 + c * t = (1 - t / T) * h 0 + (t / T) * (h 0 + c * T) := by
          have hTne : T ≠ 0 := hTeq
          field_simp
          ring
        rw [hconv]
        have hw1 : 0 ≤ (1 : ℝ) - t / T := by
          have hle : t / T ≤ 1 := (div_le_one hTpos).mpr ht.2
          linarith
        have hw2 : 0 ≤ t / T := div_nonneg ht.1 hT
        have hsum : (1 - t / T) + t / T = 1 := by ring
        calc |(1 - t / T) * h 0 + (t / T) * (h 0 + c * T)|
            ≤ |(1 - t / T) * h 0| + |(t / T) * (h 0 + c * T)| :=
              abs_add_le ((1 - t / T) * h 0) ((t / T) * (h 0 + c * T))
          _ = (1 - t / T) * |h 0| + (t / T) * |h 0 + c * T| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hw1, abs_of_nonneg hw2]
          _ ≤ (1 - t / T) * hmax + (t / T) * hmax := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hh0 hw1
              · exact mul_le_mul_of_nonneg_left hhT hw2
          _ = hmax := by
              rw [← add_mul, hsum, one_mul]

/-- A constant command reaches a finite momentum limit: applied at every `t ≥ 0` from
`|h 0| ≤ hmax`, a command `c ≠ 0` brings the wheel momentum to the limit, `|h T_sat| = hmax`, at a
finite time `T_sat ≥ 0`, and the command is inadmissible on every horizon `[0, T]` with
`T > T_sat`, whatever the command limit `umax`. -/
lemma constCommand_momentum_limit {umax hmax c : ℝ} {h : ℝ → ℝ} (hc : c ≠ 0)
    (hh : ∀ t ∈ Ici (0 : ℝ), HasDerivAt h c t) (h0 : |h 0| ≤ hmax) :
    ∃ Tsat, 0 ≤ Tsat ∧ |h Tsat| = hmax ∧
      ∀ T, Tsat < T → ¬ WheelAdmissible umax hmax T (fun _ => c) h := by
  have hform : ∀ t : ℝ, 0 ≤ t → h t = h 0 + c * t := by
    intro t ht0
    exact constCommand_eq (T := t) (fun s hs => hh s (Set.mem_Ici.mpr hs.1)) t ⟨ht0, le_refl t⟩
  have hhmax : 0 ≤ hmax := le_trans (abs_nonneg _) h0
  by_cases hcpos : 0 < c
  · refine ⟨(hmax - h 0) / c, ?_, ?_, ?_⟩
    · apply div_nonneg _ (le_of_lt hcpos)
      have hle : h 0 ≤ hmax := le_trans (le_abs_self _) h0
      linarith
    · have hTsat0 : 0 ≤ (hmax - h 0) / c := by
        apply div_nonneg _ (le_of_lt hcpos)
        have hle : h 0 ≤ hmax := le_trans (le_abs_self _) h0
        linarith
      rw [hform _ hTsat0]
      have e : h 0 + c * ((hmax - h 0) / c) = hmax := by field_simp; ring
      rw [e, abs_of_nonneg hhmax]
    · rintro T hT ⟨-, h_adm⟩
      have hTsat0 : 0 ≤ (hmax - h 0) / c := by
        apply div_nonneg _ (le_of_lt hcpos)
        have hle : h 0 ≤ hmax := le_trans (le_abs_self _) h0
        linarith
      have hT0 : 0 ≤ T := le_trans hTsat0 (le_of_lt hT)
      have hmem : T ∈ Icc 0 T := ⟨hT0, le_refl T⟩
      obtain ⟨-, hhT⟩ := h_adm T hmem
      rw [hform T hT0] at hhT
      have hmul : c * ((hmax - h 0) / c) < c * T := mul_lt_mul_of_pos_left hT hcpos
      have e : c * ((hmax - h 0) / c) = hmax - h 0 := by field_simp
      have hgt : hmax < h 0 + c * T := by linarith
      have hcon : hmax < |h 0 + c * T| := lt_of_lt_of_le hgt (le_abs_self _)
      linarith
  · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc
    refine ⟨(-hmax - h 0) / c, ?_, ?_, ?_⟩
    · apply div_nonneg_of_nonpos _ (le_of_lt hcneg)
      have h1 : -h 0 ≤ hmax := le_trans (neg_le_abs _) h0
      linarith
    · have hTsat0 : 0 ≤ (-hmax - h 0) / c := by
        apply div_nonneg_of_nonpos _ (le_of_lt hcneg)
        have h1 : -h 0 ≤ hmax := le_trans (neg_le_abs _) h0
        linarith
      rw [hform _ hTsat0]
      have e : h 0 + c * ((-hmax - h 0) / c) = -hmax := by field_simp; ring
      rw [e, abs_neg, abs_of_nonneg hhmax]
    · rintro T hT ⟨-, h_adm⟩
      have hTsat0 : 0 ≤ (-hmax - h 0) / c := by
        apply div_nonneg_of_nonpos _ (le_of_lt hcneg)
        have h1 : -h 0 ≤ hmax := le_trans (neg_le_abs _) h0
        linarith
      have hT0 : 0 ≤ T := le_trans hTsat0 (le_of_lt hT)
      have hmem : T ∈ Icc 0 T := ⟨hT0, le_refl T⟩
      obtain ⟨-, hhT⟩ := h_adm T hmem
      rw [hform T hT0] at hhT
      have hmul : c * T < c * ((-hmax - h 0) / c) := mul_lt_mul_of_neg_left hT hcneg
      have e : c * ((-hmax - h 0) / c) = -hmax - h 0 := by field_simp
      have hlt : h 0 + c * T < -hmax := by linarith
      have h2 := neg_abs_le (h 0 + c * T)
      have hcon : hmax < |h 0 + c * T| := by linarith
      linarith

end Mechanics.AttitudePorts
