/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.PowerPorts
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Particle power-port checks

Concrete consumers of `PhyslibExt.Mechanics.PowerPorts`: mass `2`, start `0` with velocity `1`
and constant force `4` over the elapsed time `1`; the unit oscillator `m = k = A = 1` over a
quarter period; the unit inverse-square field along a radial path that avoids the centre; and a
planar rigid body (mass `2`, inertia `3`) under the force `4` and the torque `6`, with the Physlib
links checked on a two-point body that glides along `e₁` while it spins up about `e₃`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No public definitions or results are introduced here; the gliding spin-up of a two-point body
is a private test fixture.

## iii. Table of contents

- A. Constant-force fixture
- B. Spring example
- C. Inverse-square field
- D. Planar rigid-body power port

## iv. References

None.

## A. Constant-force fixture

-/

open PhyslibExt.Mechanics.PowerPorts

/-- Mass `2`, start `0` with velocity `1`, force `4 ≠ 0`, elapsed time `1 > 0`: final velocity
`3`, final position `2`, work `8` (both as the integrated power and as the change of kinetic
energy), and impulse `4`. -/
example :
    constForceVelocity (E := ℝ) 2 1 4 1 = 3 ∧ constForcePosition (E := ℝ) 2 0 1 4 1 = 2 ∧
      ∫ t in (0 : ℝ)..1, inner ℝ (4 : ℝ) (constForceVelocity (E := ℝ) 2 1 4 t) = 8 ∧
      2 * ‖constForceVelocity (E := ℝ) 2 1 4 1‖ ^ 2 / 2 -
          2 * ‖constForceVelocity (E := ℝ) 2 1 4 0‖ ^ 2 / 2 = 8 ∧
      (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 1 - (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 0
        = 4 := by
  have hm : (0 : ℝ) < 2 := by norm_num
  have hv1 : constForceVelocity (E := ℝ) 2 1 4 1 = 3 := by
    simp [constForceVelocity, smul_eq_mul]
    norm_num
  have hx1 : constForcePosition (E := ℝ) 2 0 1 4 1 = 2 := by
    simp [constForcePosition, smul_eq_mul]
    norm_num
  have hv0 : constForceVelocity (E := ℝ) 2 1 4 0 = 1 := by
    simp [constForceVelocity, smul_eq_mul]
  have hK : 2 * ‖constForceVelocity (E := ℝ) 2 1 4 1‖ ^ 2 / 2 -
      2 * ‖constForceVelocity (E := ℝ) 2 1 4 0‖ ^ 2 / 2 = 8 := by
    rw [hv1, hv0]
    norm_num [Real.norm_eq_abs]
  have hwork := (constForce_work (m := 2) hm (0 : ℝ) (1 : ℝ) (4 : ℝ) (0 : ℝ) (1 : ℝ)).1
  have hwork8 : ∫ t in (0 : ℝ)..1, inner ℝ (4 : ℝ) (constForceVelocity (E := ℝ) 2 1 4 t) = 8 :=
    hwork.trans hK
  have himp : (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 1 -
      (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 0 = 4 := by
    rw [← constForce_impulse (E := ℝ) hm (1 : ℝ) (4 : ℝ) 0 1]
    simp
  exact ⟨hv1, hx1, hwork8, hK, himp⟩

/-- Newton's law on the fixture trajectory: `2 • x'' = 4`, so the acceleration is `2`. -/
example (t : ℝ) : deriv (deriv (constForcePosition (E := ℝ) 2 0 1 4)) t = 2 := by
  have h := (constForce_actual_trajectory (E := ℝ) (by norm_num : (0 : ℝ) < 2) 0 1 4).2.2 t
  rw [smul_eq_mul] at h
  linarith

/-- Power port at the start of the fixture: the kinetic energy grows at `⟪4, 1⟫ = 4`. -/
example : HasDerivAt (fun s => 2 * ‖constForceVelocity (E := ℝ) 2 1 4 s‖ ^ 2 / 2) 4 0 := by
  have h := constForce_power_port (E := ℝ) (by norm_num : (0 : ℝ) < 2) 1 4 0
  have hp : inner ℝ (4 : ℝ) (constForceVelocity (E := ℝ) 2 1 4 0) = 4 := by
    simp [constForceVelocity]
  rwa [hp] at h

/-- Impulse over the fixture interval is the change of momentum. -/
example : ∫ _ in (0 : ℝ)..1, (4 : ℝ) =
    (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 1 - (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 0 :=
  constForce_impulse (E := ℝ) (by norm_num) 1 4 0 1

/-! ## B. Spring example -/

/-- Spring power at the start of the unit oscillator: the mass starts at rest. -/
example : HasDerivAt (fun s : ℝ => 1 * ‖-1 * 1 * Real.sin (1 * s)‖ ^ 2 / 2)
    (inner ℝ (-1 * (1 * Real.cos (1 * 0))) (-1 * 1 * Real.sin (1 * 0))) 0 :=
  spring_power_port (m := 1) (k := 1) (A := 1) (ω := 1) one_pos one_pos (by simp) 0

/-- Spring work over a quarter period of the unit oscillator: the kinetic energy rises from `0`
to `1 / 2`, and the potential `x ^ 2 / 2 + C` falls by `1 / 2` whatever the constant `C`. -/
example (C : ℝ) :
    ∫ t in (0 : ℝ)..(Real.pi / 2),
        inner ℝ (-1 * (1 * Real.cos (1 * t))) (-1 * 1 * Real.sin (1 * t)) = 1 / 2 ∧
      -((1 * (1 * Real.cos (1 * (Real.pi / 2)))) ^ 2 / 2 + C -
          ((1 * (1 * Real.cos (1 * 0))) ^ 2 / 2 + C)) = 1 / 2 := by
  have h := spring_work (m := 1) (k := 1) (A := 1) (ω := 1) one_pos one_pos (by simp)
    0 (Real.pi / 2) C
  refine ⟨?_, ?_⟩
  · rw [h.1]
    norm_num
  · norm_num

/-! ## C. Inverse-square field -/

/-- Inverse-square work along the radial path `γ t = 1 + t` on `[0, 1]`, which never meets the
centre: the potential `-1 / ‖y‖` rises from `-1` to `-1 / 2`, so the work is `-1 / 2`. -/
example : ∫ t in (0 : ℝ)..1,
    inner ℝ (-OrbitalPerturbations.inverseSquareField 1 (1 + t : ℝ)) (1 : ℝ) = -1 / 2 := by
  have hcont : ContinuousOn
      (fun t : ℝ => inner ℝ (-OrbitalPerturbations.inverseSquareField 1 (1 + t : ℝ)) (1 : ℝ))
      (Set.uIcc 0 1) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h1 : (1 + t : ℝ) ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hn : ‖(1 + t : ℝ)‖ ^ 3 ≠ 0 := pow_ne_zero 3 (norm_ne_zero_iff.mpr h1)
    have hd : ContinuousAt (fun s : ℝ => ‖(1 + s : ℝ)‖ ^ 3) t := by fun_prop
    have hf : ContinuousAt (fun s : ℝ => 1 / ‖(1 + s : ℝ)‖ ^ 3) t :=
      continuousAt_const.div hd hn
    have hg : ContinuousAt (fun s : ℝ => (1 + s : ℝ)) t := by fun_prop
    simp only [OrbitalPerturbations.inverseSquareField]
    exact ((hf.smul hg).neg.inner continuousAt_const).continuousWithinAt
  rw [inverseSquare_work (γ := fun t : ℝ => 1 + t) (γ' := fun _ => 1)
    (fun t _ => by simpa using (hasDerivAt_id t).const_add 1)
    (fun t ht h => by
      rw [Set.uIcc_of_le zero_le_one] at ht
      linarith [ht.1])
    hcont.intervalIntegrable]
  norm_num

/-- On the line, the unit inverse-square field at `2` is `1 / 4`, the gradient there of
`-1 / ‖y‖`. -/
example : HasGradientAt (fun y : ℝ => -1 / ‖y‖) (1 / 4) 2 := by
  have h := hasGradientAt_inverseSquarePotential (μ := (1 : ℝ)) (x := (2 : ℝ)) two_ne_zero
  convert h using 1
  norm_num [OrbitalPerturbations.inverseSquareField]

/-- The unit inverse-square potential on the line has no limit at the centre. -/
example : ¬ ContinuousAt (fun y : ℝ => -1 / ‖y‖) 0 :=
  inverseSquarePotential_not_continuousAt_zero one_ne_zero

/-! ## D. Planar rigid-body power port -/

open scoped Matrix Time
open _root_.Mechanics.RigidMotionPorts _root_.Units.EngineeringFrames

/-- The fixture velocity `1 + 2 t` is smooth. -/
private lemma fixtureVelocity_contDiff : ContDiff ℝ 1 (constForceVelocity (E := ℝ) 2 1 4) := by
  unfold constForceVelocity
  fun_prop

/-- The fixture angle `t + t²` is smooth. -/
private lemma fixtureAngle_contDiff : ContDiff ℝ 2 (constForcePosition (E := ℝ) 3 0 1 6) := by
  unfold constForcePosition
  fun_prop

/-- The fixture velocity has the acceleration `4 / 2 = 2`. -/
private lemma fixtureVelocity_deriv (s : ℝ) : deriv (constForceVelocity (E := ℝ) 2 1 4) s = 2 := by
  rw [(constForceVelocity_hasDerivAt (E := ℝ) 2 1 4 s).deriv]
  norm_num

/-- The fixture angle has the angular acceleration `6 / 3 = 2`. -/
private lemma fixtureAngle_deriv_deriv (s : ℝ) :
    deriv (deriv (constForcePosition (E := ℝ) 3 0 1 6)) s = 2 := by
  have h := (constForce_actual_trajectory (E := ℝ) (by norm_num : (0 : ℝ) < 3) 0 1 6).2.2 s
  rw [smul_eq_mul] at h
  linarith

/-- Nonzero translation and angular acceleration: mass `2` started with velocity `1` under the
force `4`, and inertia `3` started at angle `0` with rate `1` under the torque `6`, have the
accelerations `V' = 2` and `θ'' = 2`, and at `t = 0` the kinetic energy grows at
`⟪4, 1⟫ + 6 · 1 = 10`. -/
example :
    deriv (constForceVelocity (E := ℝ) 2 1 4) 0 = 2 ∧
      deriv (deriv (constForcePosition (E := ℝ) 3 0 1 6)) 0 = 2 ∧
      HasDerivAt (fun s => 2 * ‖constForceVelocity (E := ℝ) 2 1 4 s‖ ^ 2 / 2 +
          3 * deriv (constForcePosition (E := ℝ) 3 0 1 6) s ^ 2 / 2) 10 0 := by
  have hθd1 : deriv (constForcePosition (E := ℝ) 3 0 1 6) 0 = 1 :=
    (constForce_actual_trajectory (E := ℝ) (by norm_num : (0 : ℝ) < 3) 0 1 6).2.1
  refine ⟨fixtureVelocity_deriv 0, fixtureAngle_deriv_deriv 0, ?_⟩
  have h := planarRigid_power_port (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 3)
    fixtureVelocity_contDiff fixtureAngle_contDiff (F := fun _ => (4 : ℝ)) (τ := fun _ => 6)
    (fun s => by rw [fixtureVelocity_deriv s]; norm_num)
    (fun s => by rw [fixtureAngle_deriv_deriv s]; norm_num) 0
  convert h using 1
  rw [hθd1]
  simp [constForceVelocity]
  norm_num

/-- A wrong torque sign fails on the fixture: at `t = 0` the kinetic energy does not grow at
`⟪4, 1⟫ + (-6) · 1 = -2`. -/
example : ¬ HasDerivAt (fun s => 2 * ‖constForceVelocity (E := ℝ) 2 1 4 s‖ ^ 2 / 2 +
    3 * deriv (constForcePosition (E := ℝ) 3 0 1 6) s ^ 2 / 2) (-2) 0 := by
  have hθd1 : deriv (constForcePosition (E := ℝ) 3 0 1 6) 0 = 1 :=
    (constForce_actual_trajectory (E := ℝ) (by norm_num : (0 : ℝ) < 3) 0 1 6).2.1
  have hv0 : constForceVelocity (E := ℝ) 2 1 4 0 = 1 := by
    simp [constForceVelocity]
  have h := planarRigid_power_port_neg_torque (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 3) fixtureVelocity_contDiff fixtureAngle_contDiff
    (F := fun _ => (4 : ℝ)) (τ := fun _ => 6)
    (fun s => by rw [fixtureVelocity_deriv s]; norm_num)
    (fun s => by rw [fixtureAngle_deriv_deriv s]; norm_num) (t := 0)
    (by rw [hθd1]; norm_num)
  rw [hθd1, hv0] at h
  convert h using 2
  norm_num

/-- Two unit point masses at `(±1, 0, 0)`. -/
private noncomputable def pairBody : RigidBody 3 where
  ρ :=
    { toFun := fun f => f ⟨![1, 0, 0]⟩ + f ⟨![-1, 0, 0]⟩
      map_add' := fun f g => by
        simp only [ContMDiffMap.coe_add, Pi.add_apply]
        ring
      map_smul' := fun r f => by
        simp only [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

/-- The pair has mass `2`, centre of mass `0` and moment of inertia `2` about the third axis. -/
private lemma pairBody_facts :
    pairBody.mass = 2 ∧ pairBody.centerOfMass = 0 ∧
      pairBody.inertiaTensorAbout pairBody.centerOfMass 2 2 = 2 := by
  have hc : pairBody.centerOfMass = 0 := by
    ext i
    fin_cases i <;> simp [RigidBody.centerOfMass, pairBody]
  refine ⟨by norm_num [RigidBody.mass, pairBody], hc, ?_⟩
  rw [hc, RigidBody.inertiaTensorAbout_zero]
  norm_num [RigidBody.inertiaTensor, pairBody, Fin.sum_univ_three]

/-- The pair glides along `e₁` at unit speed while it spins up about `e₃` from rest: centre of
mass `(t, 0, 0)`, orientation `Rz(t² / 2)`. -/
private noncomputable def pairSpinGlide : RigidBodyMotion 3 where
  toRigidBody := pairBody
  comTrajectory := fun s => ⟨![s.val, 0, 0]⟩
  orientation := fun t => ⟨rotZ (t.val ^ 2 / 2), rotZ_mem_specialOrthogonalGroup _⟩

/-- The spin angle `x ↦ x² / 2` has derivative `x`. -/
private lemma hasDerivAt_spinAngle (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
  have := (hasDerivAt_pow 2 x).div_const 2
  convert this using 1
  push_cast
  ring

/-- Every entry of the orientation is smooth. -/
private lemma contDiff_pairSpinGlide_orientation_apply (i j : Fin 3) :
    ContDiff ℝ 2 (fun s => (pairSpinGlide.orientation s).1 i j) := by
  have hθ : ContDiff ℝ 2 (fun s : Time => s.val ^ 2 / 2) := by fun_prop
  have hc := Real.contDiff_cos.comp hθ
  have hs := Real.contDiff_sin.comp hθ
  fin_cases i <;> fin_cases j <;> simp only [pairSpinGlide, rotZ] <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;>
    first
      | exact hc
      | exact hs
      | exact hs.neg
      | exact contDiff_const

/-- The orientation is differentiable, with the default matrix instances. -/
private lemma differentiableAt_pairSpinGlide_orientation (t : Time) :
    DifferentiableAt ℝ (fun s => (pairSpinGlide.orientation s).1) t := by
  have h : DifferentiableAt ℝ (fun s => Matrix.of.symm (pairSpinGlide.orientation s).1) t :=
    differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j =>
      ((contDiff_pairSpinGlide_orientation_apply i j).differentiable (by norm_num)) t
  exact h

/-- The body angular velocity is `(0, 0, t)`. -/
private lemma pairSpinGlide_bodyAngularVelocity (t : Time) :
    pairSpinGlide.bodyAngularVelocity t = ![0, 0, t.val] := by
  have hθ := hasDerivAt_spinAngle t.val
  have dc : ∂ₜ (fun s : Time => Real.cos (s.val ^ 2 / 2)) t =
      -Real.sin (t.val ^ 2 / 2) * t.val :=
    Time.deriv_eq_of_hasDerivAt ((Real.hasDerivAt_cos _).comp t.val hθ)
  have ds : ∂ₜ (fun s : Time => Real.sin (s.val ^ 2 / 2)) t =
      Real.cos (t.val ^ 2 / 2) * t.val :=
    Time.deriv_eq_of_hasDerivAt ((Real.hasDerivAt_sin _).comp t.val hθ)
  have dns : ∂ₜ (fun s : Time => -Real.sin (s.val ^ 2 / 2)) t =
      -(Real.cos (t.val ^ 2 / 2) * t.val) :=
    Time.deriv_eq_of_hasDerivAt ((Real.hasDerivAt_sin _).comp t.val hθ).neg
  have hd : ∂ₜ (fun s => (pairSpinGlide.orientation s).1) t =
      !![-Real.sin (t.val ^ 2 / 2) * t.val, -(Real.cos (t.val ^ 2 / 2) * t.val), 0;
        Real.cos (t.val ^ 2 / 2) * t.val, -Real.sin (t.val ^ 2 / 2) * t.val, 0; 0, 0, 0] := by
    ext i j
    refine (Time.deriv_matrix_apply _ t (differentiableAt_pairSpinGlide_orientation t) i
      j).symm.trans ?_
    fin_cases i <;> fin_cases j <;> simp only [pairSpinGlide, rotZ] <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
        Matrix.cons_val_fin_one] <;>
      first
        | exact dc
        | exact ds
        | exact dns
        | exact Time.deriv_const _
  have h : pairSpinGlide.bodyAngularVelocity t = Matrix.crossProductVee
      (((pairSpinGlide.orientation t : Matrix (Fin 3) (Fin 3) ℝ))ᵀ *
        ∂ₜ (fun s => (pairSpinGlide.orientation s).1) t) := rfl
  have hR : ((pairSpinGlide.orientation t : Matrix (Fin 3) (Fin 3) ℝ)) =
      rotZ (t.val ^ 2 / 2) := rfl
  rw [h, hd, hR]
  have hcs := Real.cos_sq_add_sin_sq (t.val ^ 2 / 2)
  ext i
  fin_cases i
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination t.val * hcs

/-- The centre of mass moves with the velocity `e₁`, of unit Euclidean norm. -/
private lemma pairSpinGlide_centerOfMassVelocity (t : Time) :
    ‖pairSpinGlide.centerOfMassVelocity t‖ = 1 := by
  have hX : Differentiable ℝ pairSpinGlide.comTrajectory := by
    refine Space.mk_differentiable.comp (differentiable_pi.mpr fun k => ?_)
    fin_cases k
    · exact Time.toRealCLM.differentiable
    · exact differentiable_const _
    · exact differentiable_const _
  have hV : ∀ j, pairSpinGlide.centerOfMassVelocity t j = ![1, 0, 0] j := by
    intro j
    rw [RigidBodyMotion.centerOfMassVelocity_eq, Time.derivVec_space hX t j]
    fin_cases j
    · exact Time.deriv_eq_of_hasDerivAt (f := fun s : Time => s.val) (hasDerivAt_id _)
    · exact Time.deriv_const _
    · exact Time.deriv_const _
  rw [EuclideanSpace.norm_eq]
  simp [hV, Fin.sum_univ_three]

-- Physlib's kinetic-energy split on an actual motion: the pair, gliding at unit speed while it
-- spins up with `ω = t` about its third axis, has `T = 2 · 1² / 2 + 2 t² / 2 = 1 + t²`.
example (t : Time) : pairSpinGlide.kineticEnergy t = 1 + t.val ^ 2 := by
  obtain ⟨hm, hc, hI⟩ := pairBody_facts
  rw [kineticEnergy_eq_planar pairSpinGlide t (by change 0 < pairBody.mass; rw [hm]; norm_num)
    (differentiableAt_pairSpinGlide_orientation t) hc (pairSpinGlide_bodyAngularVelocity t),
    pairSpinGlide_centerOfMassVelocity]
  change pairBody.mass * 1 ^ 2 / 2 + pairBody.inertiaTensorAbout pairBody.centerOfMass 2 2 *
    t.val ^ 2 / 2 = 1 + t.val ^ 2
  rw [hm, hI]
  ring

-- The axial torque balance on the same motion: whatever torque realizes the balance law, its
-- axial body component is `J ω' = 2 · 1 = 2`, the torque that spins the pair up.
example (t : Time) :
    inertialToBodyVec (pairSpinGlide.orientation t)
      (∂ₜ (comAngularMomentum pairSpinGlide) t) 2 = 2 := by
  obtain ⟨-, hc, hI⟩ := pairBody_facts
  have h := axial_torque_balance pairSpinGlide isOpen_univ
    (fun i j => (contDiff_pairSpinGlide_orientation_apply i j).contDiffOn) hc
    (ω := fun s => s.val) (fun s _ => pairSpinGlide_bodyAngularVelocity s) (Set.mem_univ t) rfl
  have hd : ∂ₜ (fun s : Time => s.val) t = 1 :=
    Time.deriv_eq_of_hasDerivAt (f := fun s : Time => s.val) (hasDerivAt_id _)
  rw [← h, hd]
  change pairBody.inertiaTensorAbout pairBody.centerOfMass 2 2 * 1 = 2
  rw [hI]
  norm_num
