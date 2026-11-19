/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.RigidMotionPorts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.Mechanics.RigidMotionPorts`

Consumers of the rotating and translating-frame acceleration and a spin-up fixture.

## i. Overview

A spin-up about the third axis, with orientation `rotZ (t ^ 2 / 2)`, has body angular velocity
`(0, 0, t)` and angular acceleration `e₃`. At `t = 0` it is momentarily at rest, so the Coriolis
and centripetal terms vanish and the acceleration of the body point `e₁` is the Euler term
`e₃ × e₁ = e₂` alone, where the constant-rate formula would give `0`. The examples apply the
public lemmas to a body-fixed vector, to a frame with constant orientation, and to the reflection
boundary.

## ii. Key results

- `spinUp`, `spinUp_bodyAngularVelocity`, `spinUp_euler_fixture` : the spin-up fixture.

## iii. Table of contents

- A. Spin-up fixture
- B. Consumers of the public lemmas

## iv. References

- `PhyslibExt.Mechanics.RigidMotionPorts` and `PhyslibExt.Units.EngineeringFrames`.
-/

@[expose] public section

open scoped Matrix
open Time

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace PhyslibExtTest.Mechanics.RigidMotionPorts

open _root_.Mechanics.RigidMotionPorts _root_.Units.EngineeringFrames

/-! ## A. Spin-up fixture -/

/-- Spin-up about the third axis for any mass distribution `B`: centre of mass at rest at the
origin, orientation the rotation by the angle `t² / 2` about the third axis (angular velocity
`t`, angular acceleration `1`). -/
noncomputable def spinUp (B : RigidBody 3) : RigidBodyMotion 3 where
  toRigidBody := B
  comTrajectory := fun _ => 0
  orientation := fun t => ⟨rotZ (t.val ^ 2 / 2), rotZ_mem_specialOrthogonalGroup _⟩

/-- The rotation about the third axis as a combination of constant matrices. -/
private lemma rotZ_eq_comb (θ : ℝ) :
    rotZ θ = Real.cos θ • !![(1 : ℝ), 0, 0; 0, 1, 0; 0, 0, 0] +
      Real.sin θ • !![(0 : ℝ), -1, 0; 1, 0, 0; 0, 0, 0] + !![(0 : ℝ), 0, 0; 0, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotZ]

/-- The spin angle `s ↦ s.val ^ 2 / 2` is smooth. -/
private lemma contDiff_spinAngle : ContDiff ℝ 2 (fun s : Time => s.val ^ 2 / 2) := by
  have h : (fun s : Time => s.val) = Time.toRealCLM := rfl
  have := ((Time.toRealCLM.contDiff (n := 2)).pow 2).div_const 2
  simpa [← h] using this

/-- The spin-up orientation is smooth. -/
private lemma contDiff_spinUp_orientation (B : RigidBody 3) :
    ContDiff ℝ 2 (fun s => ((spinUp B).orientation s : Matrix (Fin 3) (Fin 3) ℝ)) := by
  have h : (fun s => ((spinUp B).orientation s : Matrix (Fin 3) (Fin 3) ℝ)) =
      fun s => Real.cos (s.val ^ 2 / 2) • !![(1 : ℝ), 0, 0; 0, 1, 0; 0, 0, 0] +
        Real.sin (s.val ^ 2 / 2) • !![(0 : ℝ), -1, 0; 1, 0, 0; 0, 0, 0] +
          !![(0 : ℝ), 0, 0; 0, 0, 0; 0, 0, 1] := by
    funext s
    exact rotZ_eq_comb _
  rw [h]
  exact (((Real.contDiff_cos.comp contDiff_spinAngle).smul contDiff_const).add
    ((Real.contDiff_sin.comp contDiff_spinAngle).smul contDiff_const)).add contDiff_const

/-- Time derivative of a scalar multiple of a constant vector. -/
private lemma deriv_smul_const_vec {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : Time → ℝ} {t : Time} (hg : DifferentiableAt ℝ g t) (v : F) :
    ∂ₜ (fun s => g s • v) t = ∂ₜ g t • v := by
  rw [Time.deriv_eq, fderiv_smul_const hg]
  simp [Time.deriv_eq]

/-- Derivative of the spin angle. -/
private lemma hasDerivAt_spinAngle (τ : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2 / 2) τ τ := by
  have := (hasDerivAt_pow 2 τ).div_const 2
  convert this using 1
  push_cast
  ring

/-- Time derivative of the spin-up orientation. -/
private lemma deriv_spinUp_orientation (B : RigidBody 3) (t : Time) :
    ∂ₜ (fun s => ((spinUp B).orientation s : Matrix (Fin 3) (Fin 3) ℝ)) t =
      (-Real.sin (t.val ^ 2 / 2) * t.val) • !![(1 : ℝ), 0, 0; 0, 1, 0; 0, 0, 0] +
        (Real.cos (t.val ^ 2 / 2) * t.val) • !![(0 : ℝ), -1, 0; 1, 0, 0; 0, 0, 0] := by
  have hc : DifferentiableAt ℝ (fun s : Time => Real.cos (s.val ^ 2 / 2)) t :=
    ((Real.contDiff_cos.comp contDiff_spinAngle).differentiable (by norm_num)) t
  have hs : DifferentiableAt ℝ (fun s : Time => Real.sin (s.val ^ 2 / 2)) t :=
    ((Real.contDiff_sin.comp contDiff_spinAngle).differentiable (by norm_num)) t
  have dc : ∂ₜ (fun s : Time => Real.cos (s.val ^ 2 / 2)) t = -Real.sin (t.val ^ 2 / 2) * t.val :=
    Time.deriv_eq_of_hasDerivAt ((Real.hasDerivAt_cos _).comp t.val (hasDerivAt_spinAngle t.val))
  have ds : ∂ₜ (fun s : Time => Real.sin (s.val ^ 2 / 2)) t = Real.cos (t.val ^ 2 / 2) * t.val :=
    Time.deriv_eq_of_hasDerivAt ((Real.hasDerivAt_sin _).comp t.val (hasDerivAt_spinAngle t.val))
  have hD : HasFDerivAt (fun s : Time =>
      Real.cos (s.val ^ 2 / 2) • !![(1 : ℝ), 0, 0; 0, 1, 0; 0, 0, 0] +
        Real.sin (s.val ^ 2 / 2) • !![(0 : ℝ), -1, 0; 1, 0, 0; 0, 0, 0] +
          !![(0 : ℝ), 0, 0; 0, 0, 0; 0, 0, 1])
      ((fderiv ℝ (fun s : Time => Real.cos (s.val ^ 2 / 2)) t).smulRight
          !![(1 : ℝ), 0, 0; 0, 1, 0; 0, 0, 0] +
        (fderiv ℝ (fun s : Time => Real.sin (s.val ^ 2 / 2)) t).smulRight
          !![(0 : ℝ), -1, 0; 1, 0, 0; 0, 0, 0]) t :=
    ((hc.hasFDerivAt.smul_const _).add (hs.hasFDerivAt.smul_const _)).add_const _
  have h : (fun s => ((spinUp B).orientation s : Matrix (Fin 3) (Fin 3) ℝ)) =
      fun s : Time => Real.cos (s.val ^ 2 / 2) • !![(1 : ℝ), 0, 0; 0, 1, 0; 0, 0, 0] +
        Real.sin (s.val ^ 2 / 2) • !![(0 : ℝ), -1, 0; 1, 0, 0; 0, 0, 0] +
          !![(0 : ℝ), 0, 0; 0, 0, 0; 0, 0, 1] := by
    funext s
    exact rotZ_eq_comb _
  rw [h, Time.deriv_eq, hD.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply]
  rw [← Time.deriv_eq, ← Time.deriv_eq, dc, ds]

/-- The spin-up has body angular velocity `(0, 0, t)`. -/
lemma spinUp_bodyAngularVelocity (B : RigidBody 3) (t : Time) :
    (spinUp B).bodyAngularVelocity t = ![0, 0, t.val] := by
  have hd := deriv_spinUp_orientation B t
  have h : (spinUp B).bodyAngularVelocity t = Matrix.crossProductVee
      ((((spinUp B).orientation t : Matrix (Fin 3) (Fin 3) ℝ))ᵀ *
        ∂ₜ (fun s => ((spinUp B).orientation s : Matrix (Fin 3) (Fin 3) ℝ)) t) := rfl
  rw [h, hd]
  have hR : (((spinUp B).orientation t : Matrix (Fin 3) (Fin 3) ℝ)) = rotZ (t.val ^ 2 / 2) := rfl
  rw [hR]
  have hcs := Real.cos_sq_add_sin_sq (t.val ^ 2 / 2)
  ext i
  fin_cases i
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination t.val * hcs

/-- Nonzero angular acceleration exposes the Euler term: at `t = 0` the spin-up is momentarily at
rest (`ω_B = 0`, so the Coriolis and centripetal terms vanish) with angular acceleration `e₃`, and
the body point `e₁` with the origin fixed at `0` has acceleration `e₂ = R (ω_B' × e₁)`, the Euler
term alone. -/
lemma spinUp_euler_fixture (B : RigidBody 3) :
    ∂ₜ (spinUp B).bodyAngularVelocity ⟨0⟩ = ![0, 0, 1] ∧
      ∂ₜ (∂ₜ (fun s => bodyToInertial 0 ((spinUp B).orientation s) ![1, 0, 0])) ⟨0⟩ =
        ![0, 1, 0] := by
  have hω : (spinUp B).bodyAngularVelocity = fun s => s.val • ![(0 : ℝ), 0, 1] := by
    funext s
    rw [spinUp_bodyAngularVelocity]
    ext i
    fin_cases i <;> simp
  have hval : DifferentiableAt ℝ (fun s : Time => s.val) ⟨0⟩ := Time.toRealCLM.differentiableAt
  have hdω : ∂ₜ (spinUp B).bodyAngularVelocity ⟨0⟩ = ![0, 0, 1] := by
    rw [hω, deriv_smul_const_vec hval,
      Time.deriv_eq_of_hasDerivAt (f := fun s : Time => s.val) (hasDerivAt_id _), one_smul]
  refine ⟨hdω, ?_⟩
  have h := deriv_deriv_bodyToInertial (spinUp B) (fun _ => (0 : Fin 3 → ℝ))
    (fun _ => ![(1 : ℝ), 0, 0]) isOpen_univ (contDiff_spinUp_orientation B).contDiffOn
    contDiffOn_const contDiffOn_const (Set.mem_univ (⟨0⟩ : Time))
  rw [h, hdω, hω]
  have hR : (((spinUp B).orientation ⟨0⟩ : Matrix (Fin 3) (Fin 3) ℝ)) =
      rotZ ((0 : ℝ) ^ 2 / 2) := rfl
  have hc0 : ∂ₜ (fun _ : Time => (0 : Fin 3 → ℝ)) = fun _ => 0 :=
    funext fun _ => Time.deriv_const _
  have hc1 : ∂ₜ (fun _ : Time => ![(1 : ℝ), 0, 0]) = fun _ => 0 :=
    funext fun _ => Time.deriv_const _
  simp only [hc0, hc1, Time.deriv_const, bodyToInertialVec, hR]
  ext i
  fin_cases i <;> simp [rotZ, cross_apply]

/-! ## B. Consumers of the public lemmas -/

-- A body-fixed vector `v` turns with the body: its inertial components have time derivative
-- `R (ω_B × v)`.
example (M : RigidBodyMotion 3) (v : Fin 3 → ℝ) (t : Time)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) :
    ∂ₜ (fun s => bodyToInertialVec (M.orientation s) v) t =
      bodyToInertialVec (M.orientation t) (M.bodyAngularVelocity t ⨯₃ v) := by
  have h := deriv_bodyToInertialVec M (fun _ => v) t hR (differentiableAt_const v)
  rwa [Time.deriv_const, zero_add] at h

-- A frame with constant orientation and a fixed origin: the angular velocity vanishes, and the
-- acceleration is the relative acceleration in inertial components.
example (M : RigidBodyMotion 3) (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hM : M.orientation = fun _ => R) (o₀ : Fin 3 → ℝ) (xB : Time → Fin 3 → ℝ)
    (hx : ContDiff ℝ 2 xB) (t : Time) :
    ∂ₜ (∂ₜ (fun s => bodyToInertial o₀ (M.orientation s) (xB s))) t =
      bodyToInertialVec R (∂ₜ (∂ₜ xB) t) := by
  have hR : ContDiffOn ℝ 2 (fun s => (M.orientation s : Matrix (Fin 3) (Fin 3) ℝ)) Set.univ := by
    rw [hM]
    exact contDiffOn_const
  have hΩ : ∀ s ∈ Set.univ, M.bodyAngularVelocity s = 0 := fun s _ => by
    rw [RigidBodyMotion.bodyAngularVelocity_of_orientation_const M R hM]
    rfl
  rw [deriv_deriv_bodyToInertial_of_const M o₀ xB 0 isOpen_univ hR hx.contDiffOn hΩ
    (Set.mem_univ t), hM]
  simp

-- The spin-up is an admissible rigid motion: its orientation is never the reflection.
example (B : RigidBody 3) (t : Time) :
    ((spinUp B).orientation t : Matrix (Fin 3) (Fin 3) ℝ) ≠ reflectX :=
  orientation_ne_reflectX (spinUp B) t

-- The spin-up is defined for every mass distribution, the zero one included; at `t = 1` it
-- turns at the unit rate.
example : ∃ B : RigidBody 3, (spinUp B).bodyAngularVelocity ⟨1⟩ = ![0, 0, 1] :=
  ⟨⟨0⟩, by rw [spinUp_bodyAngularVelocity]⟩

end PhyslibExtTest.Mechanics.RigidMotionPorts
