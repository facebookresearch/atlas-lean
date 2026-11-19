/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.RigidMotionPorts
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.Mechanics.RigidMotionPorts`

Consumers of the rotating and translating-frame acceleration, of the angular momentum about the
centre of mass and of Euler's equations, with a spin-up fixture and a four-point body.

## i. Overview

A spin-up about the third axis, with orientation `rotZ (t ^ 2 / 2)`, has body angular velocity
`(0, 0, t)` and angular acceleration `e₃`. At `t = 0` it is momentarily at rest, so the Coriolis
and centripetal terms vanish and the acceleration of the body point `e₁` is the Euler term
`e₃ × e₁ = e₂` alone, where the constant-rate formula would give `0`. The examples apply the
public lemmas to a body-fixed vector, to a frame with constant orientation, and to the reflection
boundary.

Four unit point masses at `(±1, 0, 0)` and `(0, ±2, 0)` form a body of mass `4` with centre of
mass `0` and unequal principal inertias `diag(8, 2, 10)`. Spun up about the third principal axis,
its angular momentum about the centre of mass is `(0, 0, 10 t)` with rate of change `(0, 0, 10)`;
about the mass point `(1, 0, 0)` the parallel-axis lemma adds the orbital term `(0, 0, 4)`; and
gliding without rotation it has no angular momentum about its centre of mass but the orbital term
`(0, 0, 4)` about the fixed point `(0, 1, 0)`.

Spun up about its third principal axis, the four-point body satisfies Euler's equations with the
body torque `(0, 0, 10)`, so the balance law gives `dL_COM/dt = (0, 0, 10)`; conversely, from the
angular momentum `(0, 0, 10 t)` the positive-definite inertia `diag(8, 2, 10)` determines the
angular acceleration `e₃`, and `L_COM · L_COM = 100 t²`. The inertia `diag(8, 2, 10)` has the
gyroscopic term `(0, 0, -6)` at `ω_B = (1, 1, 0)`; the singular inertia `diag(1, 1, 0)` and the
inertia `diag(-8, -2, -10)` of a negative mass functional are not positive definite. Gliding
without rotation, the four-point body is torque free.

Driven about its third principal axis from the rate `1` with the angular acceleration `2`, the
four-point body has `ω_B = (0, 0, 1 + 2 t)` and needs the torque `(0, 0, 20)`, which delivers the
shaft power `20 (1 + 2 t)`; the sign-flipped torque fails, and with zero initial rate and unit
angular acceleration the construction has the body angular velocity of the spin-up.

The file activates no matrix norm: every regularity fact is stated and proved as a client would,
with Mathlib's default instances on matrices or entry by entry.

## ii. Key results

- `spinUp`, `spinUp_bodyAngularVelocity`, `spinUp_euler_fixture` : the spin-up fixture.
- `fourPointBody` : a four-point body with unequal principal inertias.
- `negFourPointBody` : a negative mass functional, whose inertia tensor is not positive definite.

## iii. Table of contents

- A. Spin-up fixture
- B. Consumers of the public lemmas
- C. Angular momentum: a four-point body
- D. Consumers of the angular-momentum lemmas
- E. Euler's equations
- F. Consumers of the Euler lemmas
- G. A constructed torque-driven rotation

## iv. References

- `PhyslibExt.Mechanics.RigidMotionPorts` and `PhyslibExt.Units.EngineeringFrames`.
-/

@[expose] public section

open scoped Matrix
open Time

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

/-- The spin angle `s ↦ s.val ^ 2 / 2` is smooth. -/
private lemma contDiff_spinAngle : ContDiff ℝ 2 (fun s : Time => s.val ^ 2 / 2) := by
  have h : (fun s : Time => s.val) = Time.toRealCLM := rfl
  have := ((Time.toRealCLM.contDiff (n := 2)).pow 2).div_const 2
  simpa [← h] using this

/-- Every entry of the spin-up orientation is smooth. -/
private lemma contDiff_spinUp_orientation_apply (B : RigidBody 3) (i j : Fin 3) :
    ContDiff ℝ 2 (fun s => ((spinUp B).orientation s).1 i j) := by
  have hc := Real.contDiff_cos.comp contDiff_spinAngle
  have hs := Real.contDiff_sin.comp contDiff_spinAngle
  fin_cases i <;> fin_cases j <;> simp only [spinUp, rotZ] <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;>
    first
      | exact hc
      | exact hs
      | exact hs.neg
      | exact contDiff_const

/-- The spin-up orientation is differentiable, stated with the default matrix instances: a client
obtains this from its entries. -/
private lemma differentiableAt_spinUp_orientation (B : RigidBody 3) (t : Time) :
    DifferentiableAt ℝ (fun s => ((spinUp B).orientation s).1) t := by
  have h : DifferentiableAt ℝ (fun s => Matrix.of.symm ((spinUp B).orientation s).1) t :=
    differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j =>
      ((contDiff_spinUp_orientation_apply B i j).differentiable (by norm_num)) t
  exact h

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

/-- Time derivative of the spin-up orientation, entry by entry. -/
private lemma deriv_spinUp_orientation (B : RigidBody 3) (t : Time) :
    ∂ₜ (fun s => ((spinUp B).orientation s).1) t =
      !![-Real.sin (t.val ^ 2 / 2) * t.val, -(Real.cos (t.val ^ 2 / 2) * t.val), 0;
        Real.cos (t.val ^ 2 / 2) * t.val, -Real.sin (t.val ^ 2 / 2) * t.val, 0; 0, 0, 0] := by
  have dc : ∂ₜ (fun s : Time => Real.cos (s.val ^ 2 / 2)) t = -Real.sin (t.val ^ 2 / 2) * t.val :=
    Time.deriv_eq_of_hasDerivAt ((Real.hasDerivAt_cos _).comp t.val (hasDerivAt_spinAngle t.val))
  have ds : ∂ₜ (fun s : Time => Real.sin (s.val ^ 2 / 2)) t = Real.cos (t.val ^ 2 / 2) * t.val :=
    Time.deriv_eq_of_hasDerivAt ((Real.hasDerivAt_sin _).comp t.val (hasDerivAt_spinAngle t.val))
  have dns : ∂ₜ (fun s : Time => -Real.sin (s.val ^ 2 / 2)) t =
      -(Real.cos (t.val ^ 2 / 2) * t.val) :=
    Time.deriv_eq_of_hasDerivAt
      ((Real.hasDerivAt_sin _).comp t.val (hasDerivAt_spinAngle t.val)).neg
  ext i j
  refine (Time.deriv_matrix_apply _ t (differentiableAt_spinUp_orientation B t) i j).symm.trans ?_
  fin_cases i <;> fin_cases j <;> simp only [spinUp, rotZ] <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;>
    first
      | exact dc
      | exact ds
      | exact dns
      | exact Time.deriv_const _

/-- The spin-up has body angular velocity `(0, 0, t)`. -/
lemma spinUp_bodyAngularVelocity (B : RigidBody 3) (t : Time) :
    (spinUp B).bodyAngularVelocity t = ![0, 0, t.val] := by
  have hd := deriv_spinUp_orientation B t
  have h : (spinUp B).bodyAngularVelocity t = Matrix.crossProductVee
      ((((spinUp B).orientation t : Matrix (Fin 3) (Fin 3) ℝ))ᵀ *
        ∂ₜ (fun s => ((spinUp B).orientation s).1) t) := rfl
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
    (fun _ => ![(1 : ℝ), 0, 0]) isOpen_univ
    (fun i j => (contDiff_spinUp_orientation_apply B i j).contDiffOn) contDiffOn_const
    contDiffOn_const (Set.mem_univ (⟨0⟩ : Time))
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
  have hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) Set.univ := fun i j => by
    simp only [hM]
    exact contDiffOn_const
  have hΩ : ∀ s ∈ Set.univ, M.bodyAngularVelocity s = 0 := fun s _ => by
    rw [RigidBodyMotion.bodyAngularVelocity_of_orientation_const M R hM]
    rfl
  rw [deriv_deriv_bodyToInertial_of_const M o₀ xB 0 isOpen_univ hR hx.contDiffOn hΩ
    (Set.mem_univ t), hM]
  simp

-- A concrete client: the spin-up's default-instance differentiability, obtained from its
-- entries, feeds the transport law, and a body-fixed vector `v` has inertial velocity
-- `R (t e₃ × v)`.
example (B : RigidBody 3) (v : Fin 3 → ℝ) (t : Time) :
    ∂ₜ (fun s => bodyToInertialVec ((spinUp B).orientation s) v) t =
      bodyToInertialVec ((spinUp B).orientation t) (![0, 0, t.val] ⨯₃ v) := by
  rw [deriv_bodyToInertialVec (spinUp B) (fun _ => v) t (differentiableAt_spinUp_orientation B t)
    (differentiableAt_const v), Time.deriv_const, zero_add, spinUp_bodyAngularVelocity]

-- Reflections are not orientations: no rigid-body motion, the spin-up included, has the
-- reflection `diag(-1, 1, 1)` as an orientation, since the reflection is not in `SO(3)`.
example (M : RigidBodyMotion 3) (t : Time) :
    (M.orientation t : Matrix (Fin 3) (Fin 3) ℝ) ≠ reflectX := fun h =>
  reflectX_not_mem_specialOrthogonalGroup (h ▸ (M.orientation t).2)

-- The spin-up is defined for every mass distribution, the zero one included; at `t = 1` it
-- turns at the unit rate.
example : ∃ B : RigidBody 3, (spinUp B).bodyAngularVelocity ⟨1⟩ = ![0, 0, 1] :=
  ⟨⟨0⟩, by rw [spinUp_bodyAngularVelocity]⟩

/-! ## C. Angular momentum: a four-point body -/

/-- A finite positive-mass body: four unit point masses at `(±1, 0, 0)` and `(0, ±2, 0)`. -/
noncomputable def fourPointBody : RigidBody 3 where
  ρ :=
    { toFun := fun f => f ⟨![1, 0, 0]⟩ + f ⟨![-1, 0, 0]⟩ + f ⟨![0, 2, 0]⟩ + f ⟨![0, -2, 0]⟩
      map_add' := fun f g => by
        simp only [ContMDiffMap.coe_add, Pi.add_apply]
        ring
      map_smul' := fun r f => by
        simp only [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

/-- The four-point body has mass `4`. -/
private lemma fourPointBody_mass : fourPointBody.mass = 4 := by
  norm_num [RigidBody.mass, fourPointBody]

/-- The four-point body has its centre of mass at the origin. -/
private lemma fourPointBody_centerOfMass : fourPointBody.centerOfMass = 0 := by
  ext i
  fin_cases i <;> simp [RigidBody.centerOfMass, fourPointBody]

/-- The inertia tensor of the four-point body about its centre of mass is `diag(8, 2, 10)`. -/
private lemma fourPointBody_inertia :
    fourPointBody.inertiaTensorAbout fourPointBody.centerOfMass =
      Matrix.diagonal ![8, 2, 10] := by
  rw [fourPointBody_centerOfMass, RigidBody.inertiaTensorAbout_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RigidBody.inertiaTensor, fourPointBody, Fin.sum_univ_three] <;> norm_num

-- The four-point body has mass `4`, centre of mass `0` and unequal principal inertias: its
-- inertia tensor about the centre of mass is `diag(8, 2, 10)`.
example :
    fourPointBody.mass = 4 ∧ fourPointBody.centerOfMass = 0 ∧
      fourPointBody.inertiaTensorAbout fourPointBody.centerOfMass =
        Matrix.diagonal ![8, 2, 10] :=
  ⟨fourPointBody_mass, fourPointBody_centerOfMass, fourPointBody_inertia⟩

-- With unequal principal inertias the gyroscopic term does not vanish: for
-- `I_B = diag(8, 2, 10)` and `ω_B = (1, 1, 0)`, `I_B ω_B = (8, 2, 0)` and
-- `ω_B × (I_B ω_B) = (0, 0, -6)`; along a motion with this constant body angular velocity,
-- `dL_COM/dt = R (0, 0, -6) ≠ 0`.
example :
    fourPointBody.inertiaTensorAbout fourPointBody.centerOfMass *ᵥ ![1, 1, 0] = ![8, 2, 0] ∧
      ![1, 1, 0] ⨯₃ (fourPointBody.inertiaTensorAbout fourPointBody.centerOfMass *ᵥ ![1, 1, 0]) =
        ![0, 0, -6] := by
  rw [fourPointBody_inertia]
  constructor
  · ext i
    fin_cases i <;> simp [Matrix.mulVec_diagonal]
  · ext i
    fin_cases i <;> norm_num [Matrix.mulVec_diagonal, cross_apply]

-- A shifted reference point needs the orbital term: about the mass point `p = (1, 0, 0)` the
-- four-point body turning with `ω = (0, 0, 1)` has angular momentum `(0, 0, 14)`, the spin term
-- `(0, 0, 10)` about the centre of mass plus the orbital term `(0, 0, 4)`.
example :
    fourPointBody.inertiaTensorAbout ⟨![1, 0, 0]⟩ *ᵥ ![0, 0, 1] = ![0, 0, 14] ∧
      fourPointBody.inertiaTensorAbout fourPointBody.centerOfMass *ᵥ ![0, 0, 1] = ![0, 0, 10] := by
  constructor
  · ext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three, RigidBody.inertiaTensorAbout,
        fourPointBody]
  · rw [fourPointBody_inertia]
    ext i
    fin_cases i <;> simp [Matrix.mulVec_diagonal]

/-! ## D. Consumers of the angular-momentum lemmas -/

-- The parallel-axis lemma on the four-point body: about the mass point `p = (1, 0, 0)`, turning
-- with `ω = e₃`, the orbital term of the total mass at the centre of mass is `(0, 0, 4)`.
example :
    fourPointBody.inertiaTensorAbout ⟨![1, 0, 0]⟩ *ᵥ ![0, 0, 1] =
      fourPointBody.inertiaTensorAbout fourPointBody.centerOfMass *ᵥ ![0, 0, 1] + ![0, 0, 4] := by
  rw [inertiaTensorAbout_mulVec_eq_add_orbital fourPointBody
    (by rw [fourPointBody_mass]; norm_num) ⟨![1, 0, 0]⟩ ![0, 0, 1], fourPointBody_mass,
    fourPointBody_centerOfMass]
  congr 1
  ext i
  fin_cases i <;> norm_num [cross_apply]

-- The four-point body spun up about its third principal axis: the angular momentum about the
-- centre of mass is `R I_B ω_B = (0, 0, 10 t)`, along the spin axis.
example (t : Time) : comAngularMomentum (spinUp fourPointBody) t = ![0, 0, 10 * t.val] := by
  have hI : (spinUp fourPointBody).inertiaTensorAbout (spinUp fourPointBody).centerOfMass =
      Matrix.diagonal ![8, 2, 10] := fourPointBody_inertia
  have hR : (((spinUp fourPointBody).orientation t : Matrix (Fin 3) (Fin 3) ℝ)) =
      rotZ (t.val ^ 2 / 2) := rfl
  rw [(comAngularMomentum_eq (spinUp fourPointBody) t
    (differentiableAt_spinUp_orientation _ t) fourPointBody_centerOfMass).2, hI, hR,
    spinUp_bodyAngularVelocity]
  ext i
  fin_cases i <;> simp [rotZ, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

-- Spinning up with unit angular acceleration about the third principal axis takes the rate of
-- change `I₃ e₃ = (0, 0, 10)` of the angular momentum about the centre of mass; on a principal
-- axis the gyroscopic term `ω_B × (I_B ω_B)` vanishes.
example (t : Time) : ∂ₜ (comAngularMomentum (spinUp fourPointBody)) t = ![0, 0, 10] := by
  have hI : (spinUp fourPointBody).inertiaTensorAbout (spinUp fourPointBody).centerOfMass =
      Matrix.diagonal ![8, 2, 10] := fourPointBody_inertia
  have hR : (((spinUp fourPointBody).orientation t : Matrix (Fin 3) (Fin 3) ℝ)) =
      rotZ (t.val ^ 2 / 2) := rfl
  have hω : (spinUp fourPointBody).bodyAngularVelocity = fun s => s.val • ![(0 : ℝ), 0, 1] := by
    funext s
    rw [spinUp_bodyAngularVelocity]
    ext i
    fin_cases i <;> simp
  have hval : DifferentiableAt ℝ (fun s : Time => s.val) t := Time.toRealCLM.differentiableAt
  have hdω : ∂ₜ (spinUp fourPointBody).bodyAngularVelocity t = ![0, 0, 1] := by
    rw [hω, deriv_smul_const_vec hval,
      Time.deriv_eq_of_hasDerivAt (f := fun s : Time => s.val) (hasDerivAt_id _), one_smul]
  rw [deriv_comAngularMomentum (spinUp fourPointBody) isOpen_univ
    (fun i j => (contDiff_spinUp_orientation_apply fourPointBody i j).contDiffOn)
    fourPointBody_centerOfMass (Set.mem_univ t), hdω, hI, hR, spinUp_bodyAngularVelocity]
  ext i
  fin_cases i <;> simp [rotZ, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cross_apply]

/-- The four-point body gliding without rotation: centre of mass at `(s, 0, 0)` at time `s`,
identity orientation. -/
private noncomputable def glide : RigidBodyMotion 3 where
  toRigidBody := fourPointBody
  comTrajectory := fun s => ⟨![s.val, 0, 0]⟩
  orientation := fun _ => 1

-- A shifted origin needs the translational orbital term: gliding without rotation, the body has
-- no angular momentum about its centre of mass, but about the fixed point `O = (0, 1, 0)` it has
-- the orbital term `m (X - O) × V = 4 (t, -1, 0) × (1, 0, 0) = (0, 0, 4)`.
example (t : Time) :
    comAngularMomentum glide t = 0 ∧ angularMomentumAbout glide ![0, 1, 0] t = ![0, 0, 4] := by
  have hL : comAngularMomentum glide t = 0 := by
    have hR : DifferentiableAt ℝ (fun s => (glide.orientation s).1) t := differentiableAt_const _
    rw [(comAngularMomentum_eq glide t hR fourPointBody_centerOfMass).2,
      RigidBodyMotion.bodyAngularVelocity_of_orientation_const glide 1 rfl]
    simp
  have hX : Differentiable ℝ glide.comTrajectory := by
    refine Space.mk_differentiable.comp (differentiable_pi.mpr fun k => ?_)
    fin_cases k
    · exact Time.toRealCLM.differentiable
    · exact differentiable_const _
    · exact differentiable_const _
  have hV : (fun j => glide.centerOfMassVelocity t j) = ![1, 0, 0] := by
    funext j
    rw [RigidBodyMotion.centerOfMassVelocity_eq, Time.derivVec_space hX t j]
    fin_cases j
    · exact Time.deriv_eq_of_hasDerivAt (f := fun s : Time => s.val) (hasDerivAt_id _)
    · exact Time.deriv_const _
    · exact Time.deriv_const _
  have hm : glide.mass ≠ 0 := by
    change fourPointBody.mass ≠ 0
    rw [fourPointBody_mass]
    norm_num
  refine ⟨hL, ?_⟩
  rw [angularMomentumAbout_eq glide hm ![0, 1, 0] t, hL, zero_add, hV]
  change fourPointBody.mass • _ = _
  rw [fourPointBody_mass]
  ext i
  fin_cases i <;> simp [glide, cross_apply]

/-! ## E. Euler's equations -/

-- A positive diagonal inertia with a nonzero gyroscopic term: `I_B = diag(8, 2, 10)` is positive
-- definite; at `ω_B = (1, 1, 0)` the gyroscopic term is `ω_B × (I_B ω_B) = (0, 0, -6)`, and without
-- torque Euler's equations have the unique solution `ω_B' = (0, 0, 3 / 5)`.
example :
    (Matrix.diagonal ![8, 2, 10] : Matrix (Fin 3) (Fin 3) ℝ).PosDef ∧
      ![1, 1, 0] ⨯₃ (Matrix.diagonal ![8, 2, 10] *ᵥ ![1, 1, 0]) = ![0, 0, -6] ∧
      ∀ a : Fin 3 → ℝ,
        Matrix.diagonal ![8, 2, 10] *ᵥ a + ![1, 1, 0] ⨯₃ (Matrix.diagonal ![8, 2, 10] *ᵥ ![1, 1, 0]) =
            0 ↔ a = ![0, 0, 3 / 5] := by
  refine ⟨Matrix.PosDef.diagonal (fun i => by fin_cases i <;> norm_num), ?_, fun a => ?_⟩
  · ext i
    fin_cases i <;> norm_num [Matrix.mulVec_diagonal, cross_apply]
  · constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      simp [Matrix.mulVec_diagonal, cross_apply] at h0 h1 h2
      ext i
      fin_cases i <;> simp <;> linarith
    · rintro rfl
      ext i
      fin_cases i <;> norm_num [Matrix.mulVec_diagonal, cross_apply]

-- Singular inertia is rejected: `diag(1, 1, 0)` is not positive definite, and at `ω_B = (1, 0, 0)`
-- Euler's equations have every `(0, 0, c)` as a solution without torque and no solution for the
-- body torque `(0, 0, 1)`.
example :
    ¬ (Matrix.diagonal ![1, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ).PosDef ∧
      (∀ c : ℝ, Matrix.diagonal ![1, 1, 0] *ᵥ ![0, 0, c] +
          ![1, 0, 0] ⨯₃ (Matrix.diagonal ![1, 1, 0] *ᵥ ![1, 0, 0]) = 0) ∧
      ¬ ∃ a : Fin 3 → ℝ, Matrix.diagonal ![1, 1, 0] *ᵥ a +
          ![1, 0, 0] ⨯₃ (Matrix.diagonal ![1, 1, 0] *ᵥ ![1, 0, 0]) = ![0, 0, 1] := by
  refine ⟨?_, fun c => ?_, ?_⟩
  · intro h
    have hx : (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
      intro h0
      have := congrFun h0 2
      simp at this
    have := h.dotProduct_mulVec_pos hx
    simp [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three] at this
  · ext i
    fin_cases i <;> simp [Matrix.mulVec_diagonal, cross_apply]
  · rintro ⟨a, ha⟩
    have := congrFun ha 2
    simp [Matrix.mulVec_diagonal, cross_apply] at this

/-- A negative mass functional: minus four unit point masses at `(±1, 0, 0)` and `(0, ±2, 0)`.
Physlib's rigid body admits any linear functional on smooth functions. -/
noncomputable def negFourPointBody : RigidBody 3 where
  ρ :=
    { toFun := fun f => -(f ⟨![1, 0, 0]⟩ + f ⟨![-1, 0, 0]⟩ + f ⟨![0, 2, 0]⟩ + f ⟨![0, -2, 0]⟩)
      map_add' := fun f g => by
        simp only [ContMDiffMap.coe_add, Pi.add_apply]
        ring
      map_smul' := fun r f => by
        simp only [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

-- Negative mass functionals do not give positive-definite inertia: the negative four-point body has
-- mass `-4`, centre of mass `0` and inertia tensor `diag(-8, -2, -10)` about it, which is not
-- positive definite.
example :
    negFourPointBody.mass = -4 ∧ negFourPointBody.centerOfMass = 0 ∧
      negFourPointBody.inertiaTensorAbout negFourPointBody.centerOfMass =
        Matrix.diagonal ![-8, -2, -10] ∧
      ¬ (negFourPointBody.inertiaTensorAbout negFourPointBody.centerOfMass).PosDef := by
  have hmass : negFourPointBody.mass = -4 := by
    norm_num [RigidBody.mass, negFourPointBody]
  have hcom : negFourPointBody.centerOfMass = 0 := by
    ext i
    fin_cases i <;> simp [RigidBody.centerOfMass, negFourPointBody]
  have hinertia : negFourPointBody.inertiaTensorAbout negFourPointBody.centerOfMass =
      Matrix.diagonal ![-8, -2, -10] := by
    rw [hcom, RigidBody.inertiaTensorAbout_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [RigidBody.inertiaTensor, negFourPointBody, Fin.sum_univ_three] <;> norm_num
  refine ⟨hmass, hcom, hinertia, ?_⟩
  rw [hinertia, Matrix.posDef_diagonal_iff]
  intro h
  have := h 0
  norm_num at this

/-! ## F. Consumers of the Euler lemmas -/

/-- The inertia `diag(8, 2, 10)` of the four-point body is positive definite. -/
private lemma posDef_diag : (Matrix.diagonal ![8, 2, 10] : Matrix (Fin 3) (Fin 3) ℝ).PosDef :=
  Matrix.PosDef.diagonal fun i => by fin_cases i <;> norm_num

/-- The inverse of `diag(8, 2, 10)` is `diag(1 / 8, 1 / 2, 1 / 10)`. -/
private lemma inv_diag : (Matrix.diagonal ![8, 2, 10] : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ =
    Matrix.diagonal ![1 / 8, 1 / 2, 1 / 10] := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> norm_num

/-- The four-point body spun up about its third principal axis has the angular momentum
`(0, 0, 10 t)` about its centre of mass. -/
private lemma comAngularMomentum_spinUp_fourPointBody :
    comAngularMomentum (spinUp fourPointBody) = fun s => s.val • ![(0 : ℝ), 0, 10] := by
  funext s
  have hI : (spinUp fourPointBody).inertiaTensorAbout (spinUp fourPointBody).centerOfMass =
      Matrix.diagonal ![8, 2, 10] := fourPointBody_inertia
  have hR : (((spinUp fourPointBody).orientation s : Matrix (Fin 3) (Fin 3) ℝ)) =
      rotZ (s.val ^ 2 / 2) := rfl
  rw [(comAngularMomentum_eq (spinUp fourPointBody) s
    (differentiableAt_spinUp_orientation _ s) fourPointBody_centerOfMass).2, hI, hR,
    spinUp_bodyAngularVelocity]
  ext i
  fin_cases i <;> simp [rotZ, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

-- Solving Euler's equations with the explicit inverse: for `I_B = diag(8, 2, 10)` and
-- `ω_B = (1, 1, 0)` without torque, `ω_B' = I_B⁻¹ (0 - ω_B × (I_B ω_B)) = (0, 0, 3 / 5)`.
example (a : Fin 3 → ℝ) :
    Matrix.diagonal ![8, 2, 10] *ᵥ a + ![1, 1, 0] ⨯₃ (Matrix.diagonal ![8, 2, 10] *ᵥ ![1, 1, 0]) =
      0 ↔ a = ![0, 0, 3 / 5] := by
  have hval : Matrix.diagonal ![1 / 8, 1 / 2, 1 / 10] *ᵥ
      ((0 : Fin 3 → ℝ) - ![1, 1, 0] ⨯₃ (Matrix.diagonal ![8, 2, 10] *ᵥ ![1, 1, 0])) =
        ![0, 0, 3 / 5] := by
    ext i
    fin_cases i <;> norm_num [Matrix.mulVec_diagonal, cross_apply]
  rw [euler_solve_iff posDef_diag, inv_diag, hval]

-- The transport lemma on an actual motion: the four-point body spun up about its third principal
-- axis satisfies Euler's equations with the body torque `(0, 0, 10)`, so the balance law gives
-- `dL_COM/dt = (0, 0, 10)`, the rate computed from the angular momentum in section D.
example (t : Time) : ∂ₜ (comAngularMomentum (spinUp fourPointBody)) t = ![0, 0, 10] := by
  have hI : (spinUp fourPointBody).inertiaTensorAbout (spinUp fourPointBody).centerOfMass =
      Matrix.diagonal ![8, 2, 10] := fourPointBody_inertia
  have hω : (spinUp fourPointBody).bodyAngularVelocity = fun s => s.val • ![(0 : ℝ), 0, 1] := by
    funext s
    rw [spinUp_bodyAngularVelocity]
    ext i
    fin_cases i <;> simp
  have hval : DifferentiableAt ℝ (fun s : Time => s.val) t := Time.toRealCLM.differentiableAt
  have hdω : ∂ₜ (spinUp fourPointBody).bodyAngularVelocity t = ![0, 0, 1] := by
    rw [hω, deriv_smul_const_vec hval,
      Time.deriv_eq_of_hasDerivAt (f := fun s : Time => s.val) (hasDerivAt_id _), one_smul]
  have hR : (((spinUp fourPointBody).orientation t : Matrix (Fin 3) (Fin 3) ℝ)) =
      rotZ (t.val ^ 2 / 2) := rfl
  rw [deriv_comAngularMomentum_eq_iff_euler (spinUp fourPointBody) isOpen_univ
    (fun i j => (contDiff_spinUp_orientation_apply fourPointBody i j).contDiffOn)
    fourPointBody_centerOfMass (Set.mem_univ t), hdω, hI, spinUp_bodyAngularVelocity]
  simp only [inertialToBodyVec, hR]
  ext i
  fin_cases i <;> simp [rotZ, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cross_apply]

-- Solving for the angular acceleration along the spin-up: the angular momentum `(0, 0, 10 t)`
-- changes at the rate `(0, 0, 10)`, and with the positive-definite inertia `diag(8, 2, 10)` the
-- balance law determines `ω_B' = I_B⁻¹ (Rᵀ (0, 0, 10) - ω_B × (I_B ω_B)) = e₃`.
example (t : Time) : ∂ₜ (spinUp fourPointBody).bodyAngularVelocity t = ![0, 0, 1] := by
  have hI : (spinUp fourPointBody).inertiaTensorAbout (spinUp fourPointBody).centerOfMass =
      Matrix.diagonal ![8, 2, 10] := fourPointBody_inertia
  have hval : DifferentiableAt ℝ (fun s : Time => s.val) t := Time.toRealCLM.differentiableAt
  have hlaw : ∂ₜ (comAngularMomentum (spinUp fourPointBody)) t = ![0, 0, 10] := by
    rw [comAngularMomentum_spinUp_fourPointBody, deriv_smul_const_vec hval,
      Time.deriv_eq_of_hasDerivAt (f := fun s : Time => s.val) (hasDerivAt_id _), one_smul]
  have hpos : ((spinUp fourPointBody).inertiaTensorAbout
      (spinUp fourPointBody).centerOfMass).PosDef := by
    rw [hI]
    exact posDef_diag
  have hR : (((spinUp fourPointBody).orientation t : Matrix (Fin 3) (Fin 3) ℝ)) =
      rotZ (t.val ^ 2 / 2) := rfl
  rw [(deriv_comAngularMomentum_eq_iff_deriv_bodyAngularVelocity (spinUp fourPointBody)
    isOpen_univ (fun i j => (contDiff_spinUp_orientation_apply fourPointBody i j).contDiffOn)
    fourPointBody_centerOfMass hpos (Set.mem_univ t) _).mp hlaw, hI, inv_diag,
    spinUp_bodyAngularVelocity]
  simp only [inertialToBodyVec, hR]
  ext i
  fin_cases i <;> simp [rotZ, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cross_apply]

-- The angular-momentum norm along the spin-up: `L_COM · L_COM = (I_B ω_B) · (I_B ω_B) = 100 t²`.
example (t : Time) :
    comAngularMomentum (spinUp fourPointBody) t ⬝ᵥ comAngularMomentum (spinUp fourPointBody) t =
      100 * t.val ^ 2 := by
  have hI : (spinUp fourPointBody).inertiaTensorAbout (spinUp fourPointBody).centerOfMass =
      Matrix.diagonal ![8, 2, 10] := fourPointBody_inertia
  rw [comAngularMomentum_dotProduct_self (spinUp fourPointBody) t
    (differentiableAt_spinUp_orientation _ t) fourPointBody_centerOfMass, hI,
    spinUp_bodyAngularVelocity]
  simp [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three]
  ring

-- Torque-free motion of an actual body: gliding without rotation, the four-point body has no
-- angular momentum about its centre of mass, so it is torque free at every time and keeps its
-- rotational kinetic energy and angular-momentum norm (both zero here).
example (s t : Time) :
    glide.toRigidBody.rotationalKineticEnergy (glide.bodyAngularVelocity s) =
        glide.toRigidBody.rotationalKineticEnergy (glide.bodyAngularVelocity t) ∧
      (glide.inertiaTensorAbout glide.centerOfMass *ᵥ glide.bodyAngularVelocity s) ⬝ᵥ
          (glide.inertiaTensorAbout glide.centerOfMass *ᵥ glide.bodyAngularVelocity s) =
        (glide.inertiaTensorAbout glide.centerOfMass *ᵥ glide.bodyAngularVelocity t) ⬝ᵥ
          (glide.inertiaTensorAbout glide.centerOfMass *ᵥ glide.bodyAngularVelocity t) := by
  have hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (glide.orientation s).1 i j) Set.univ :=
    fun i j => contDiffOn_const
  have hL : comAngularMomentum glide = fun _ => 0 := by
    funext τ
    have hRd : DifferentiableAt ℝ (fun s => (glide.orientation s).1) τ := differentiableAt_const _
    rw [(comAngularMomentum_eq glide τ hRd fourPointBody_centerOfMass).2,
      RigidBodyMotion.bodyAngularVelocity_of_orientation_const glide 1 rfl]
    simp
  exact torqueFree_conserved glide isOpen_univ isPreconnected_univ hR fourPointBody_centerOfMass
    (fun τ _ => by rw [hL]; exact Time.deriv_const 0) (Set.mem_univ s) (Set.mem_univ t)


/-! ## G. A constructed torque-driven rotation -/

-- The four-point body (centre of mass `0`, inertia `diag(8, 2, 10)` about it) driven from the rate
-- `ω₀ = 1` with the angular acceleration `α = 2`: `ω_B(t) = (0, 0, 1 + 2 t)`, `ω_B' = (0, 0, 2)`,
-- and the balance law needs `dL_COM/dt = (0, 0, 20)`.
example (t : Time) :
    (fixedAxisMotion fourPointBody 1 2).bodyAngularVelocity t = ![0, 0, 1 + 2 * t.val] ∧
      ∂ₜ (fixedAxisMotion fourPointBody 1 2).bodyAngularVelocity t = ![0, 0, 2] ∧
      ∂ₜ (comAngularMomentum (fixedAxisMotion fourPointBody 1 2)) t = ![0, 0, 20] := by
  obtain ⟨h1, h2⟩ := deriv_comAngularMomentum_fixedAxisMotion fourPointBody_centerOfMass
    fourPointBody_inertia 1 2 t
  refine ⟨?_, deriv_fixedAxisMotion_bodyAngularVelocity _ 1 2 t, ?_⟩
  · rw [fixedAxisMotion_bodyAngularVelocity, (deriv_fixedAxisAngle 1 2 t).1]
  · rw [h1, h2]
    ext i
    fin_cases i <;> norm_num [fixedAxisTorque]

-- The constructed orientation is `C²` entry by entry on all times, the regularity the transport and
-- Euler lemmas take.
example (B : RigidBody 3) (ω₀ α : ℝ) (i j : Fin 3) :
    ContDiffOn ℝ 2 (fun s => ((fixedAxisMotion B ω₀ α).orientation s).1 i j) Set.univ :=
  (contDiff_infty.1 (contDiff_fixedAxisMotion_orientation_apply B ω₀ α i j) 2).contDiffOn

-- At `t = 0` the drive with the initial rate `1` has the angle `0` and the rate `1`, so `Ṙ(0)` is
-- the generator of rotations about `e₃`.
example (B : RigidBody 3) :
    ∂ₜ (fun s => ((fixedAxisMotion B 1 2).orientation s).1) 0 =
      !![0, -1, 0; 1, 0, 0; 0, 0, 0] := by
  have h0 : fixedAxisAngle 1 2 0 = 0 := by simp [fixedAxisAngle, Time.zero_val]
  rw [deriv_fixedAxisMotion_orientation, (deriv_fixedAxisAngle 1 2 0).1, h0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Time.zero_val]

-- With zero initial rate and unit angular acceleration the construction has the body angular
-- velocity `(0, 0, t)` of the spin-up of section A.
example (B : RigidBody 3) (t : Time) :
    (fixedAxisMotion B 0 1).bodyAngularVelocity t = (spinUp B).bodyAngularVelocity t := by
  rw [fixedAxisMotion_bodyAngularVelocity, (deriv_fixedAxisAngle 0 1 t).1,
    spinUp_bodyAngularVelocity]
  simp

-- Euler's equations on the driven four-point body: the inertia `diag(8, 2, 10)` and the angular
-- acceleration `2` need the body torque `(0, 0, 20)`.
example (t : Time) :
    (fixedAxisMotion fourPointBody 1 2).inertiaTensorAbout
          (fixedAxisMotion fourPointBody 1 2).centerOfMass *ᵥ
        ∂ₜ (fixedAxisMotion fourPointBody 1 2).bodyAngularVelocity t +
      (fixedAxisMotion fourPointBody 1 2).bodyAngularVelocity t ⨯₃
        ((fixedAxisMotion fourPointBody 1 2).inertiaTensorAbout
            (fixedAxisMotion fourPointBody 1 2).centerOfMass *ᵥ
          (fixedAxisMotion fourPointBody 1 2).bodyAngularVelocity t) = ![0, 0, 20] := by
  rw [fixedAxisMotion_euler fourPointBody_inertia 1 2 t]
  ext i
  fin_cases i <;> norm_num [fixedAxisTorque]

-- The torque port of the driven four-point body: the rotational kinetic energy `5 (1 + 2 t)²`
-- changes at the shaft power `20 (1 + 2 t)` of the torque `20` at the angular velocity `1 + 2 t`.
example (t : Time) :
    ∂ₜ (fun s => fourPointBody.rotationalKineticEnergy
        ((fixedAxisMotion fourPointBody 1 2).bodyAngularVelocity s)) t = 20 * (1 + 2 * t.val) := by
  obtain ⟨-, h, hP⟩ := fixedAxisMotion_power_port fourPointBody_centerOfMass
    fourPointBody_inertia 1 2 t
  rw [h, hP, _root_.Units.EngineeringQuantities.shaftPower_val, (deriv_fixedAxisAngle 1 2 t).1]
  norm_num

-- A nonzero angular acceleration needs a nonzero torque: for the four-point body (`I_zz = 10`)
-- and `α = 2` the port torque is nonzero, and the balance law fails for the sign-flipped torque.
example (t : Time) :
    fixedAxisTorque 10 2 ≠ 0 ∧
      ∂ₜ (comAngularMomentum (fixedAxisMotion fourPointBody 1 2)) t ≠ -fixedAxisTorque 10 2 :=
  ⟨(fixedAxisMotion_torque_ne_zero (ω₀ := 1) fourPointBody_centerOfMass fourPointBody_inertia
      (by norm_num) (by norm_num) t).1,
    (fixedAxisMotion_neg_torque (ω₀ := 1) fourPointBody_centerOfMass fourPointBody_inertia
      (by norm_num) (by norm_num) t).2⟩

end PhyslibExtTest.Mechanics.RigidMotionPorts
