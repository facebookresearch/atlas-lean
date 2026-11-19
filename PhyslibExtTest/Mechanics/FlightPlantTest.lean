/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.FlightPlant
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Tests for `PhyslibExt.Mechanics.FlightPlant`

Consumers of the translational correspondence, of the six-degree-of-freedom package and of the
coefficient-map wrapper: straight flight, the admitted domain of a lift map, and a steady level
turn.

## i. Overview

Straight flight with identity orientation and position `(t, 0, 0)` has the nonzero position rate
`(1, 0, 0)`, but its reduced state, the body velocity `(1, 0, 0)` and the body angular velocity
`0`, has zero rate: with unit mass, gravity `(0, 0, -1)` and a lift map giving the body force
`(0, 0, 1)` and no moment, the plant holds and its residual vanishes. The lift map is admitted
only at states with positive forward body velocity, and the plant fails elsewhere.

A steady level turn at unit speed and unit yaw rate, with orientation `Rz(t)` and position
`(sin t, 1 - cos t, 0)` on the circle of radius `1` about `(0, 1, 0)`, has the constant body
velocity `(1, 0, 0)`, the body angular velocity `(0, 0, 1)` and the gyroscopic term
`ω_B × v_B = (0, 1, 0)`, toward the centre of the turn. Differentiating the position directly
gives `X'' = (-sin t, cos t, 0) = R (0, 1, 1) + (0, 0, -1)`, the inertial law with the body force
`(0, 1, 1)`, and the translational correspondence turns it into the body equation; with the body
force `(0, -1, 1)`, away from the centre, the law fails.

## ii. Key results

- `straightFlight`, `straightPosition`, `liftMaps`, `straightFlight_fixture`,
  `straightFlight_balanceLaws`, `liftMaps_not_sixDofPlant` : the straight-flight fixture.

## iii. Table of contents

- A. Straight flight
- B. Consumers of the public lemmas
- C. A steady level turn

## iv. References

- `PhyslibExt.Mechanics.FlightPlant` and `PhyslibExt.Mechanics.RigidMotionPorts`.
-/

@[expose] public section

open scoped Matrix
open Time

namespace PhyslibExtTest.Mechanics.FlightPlant

open _root_.Mechanics.FlightPlant _root_.Mechanics.RigidMotionPorts _root_.Units.EngineeringFrames

/-! ## A. Straight flight -/

/-- Straight flight of the mass distribution `B`: identity orientation and centre of mass at
`(s, 0, 0)` at time `s`. -/
noncomputable def straightFlight (B : RigidBody 3) : RigidBodyMotion 3 where
  toRigidBody := B
  comTrajectory := fun s => ⟨![s.val, 0, 0]⟩
  orientation := fun _ => 1

/-- The inertial position `(s, 0, 0)` of straight flight at time `s`. -/
noncomputable def straightPosition (s : Time) : Fin 3 → ℝ := ![s.val, 0, 0]

/-- Lift maps for unit mass in the gravity `(0, 0, -1)`: the body force `(0, 0, 1)` and no moment,
admitted at the states (body velocities) with positive forward component. -/
def liftMaps : ForceMomentMaps (Fin 3 → ℝ) where
  domain := {v | 0 < v 0}
  force := fun _ => ![0, 0, 1]
  moment := fun _ => 0

/-- The orientation of straight flight is constant, hence `C²` entry by entry. -/
private lemma contDiffOn_straightFlight_orientation (B : RigidBody 3) (i j : Fin 3) :
    ContDiffOn ℝ 2 (fun s => ((straightFlight B).orientation s).1 i j) Set.univ :=
  contDiffOn_const

/-- The position of straight flight is smooth. -/
private lemma contDiffOn_straightPosition : ContDiffOn ℝ 2 straightPosition Set.univ := by
  refine (contDiff_pi.2 fun i => ?_).contDiffOn
  fin_cases i
  · exact Time.toRealCLM.contDiff
  · exact contDiff_const
  · exact contDiff_const

/-- The position of straight flight has rate `(1, 0, 0)`. -/
private lemma deriv_straightPosition (t : Time) : ∂ₜ straightPosition t = ![1, 0, 0] := by
  have hγ : HasDerivAt (fun x : ℝ => ![x, 0, 0]) ![1, 0, 0] (Time.toRealCLE t) := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hasDerivAt_id' (Time.toRealCLE t)
    · simpa using hasDerivAt_const (Time.toRealCLE t) (0 : ℝ)
    · simpa using hasDerivAt_const (Time.toRealCLE t) (0 : ℝ)
  have h : straightPosition = fun s => (fun x : ℝ => ![x, 0, 0]) (Time.toRealCLE s) := rfl
  rw [h]
  exact Time.deriv_comp_toRealCLE_of_hasDerivAt _ t _ hγ

/-- The body velocity of straight flight is constant, `(1, 0, 0)`. -/
private lemma bodyVelocity_straightFlight (B : RigidBody 3) :
    bodyVelocity (straightFlight B) straightPosition = fun _ => ![1, 0, 0] := by
  funext s
  rw [bodyVelocity, deriv_straightPosition]
  change (1 : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *ᵥ _ = _
  simp

/-- Straight flight does not turn. -/
private lemma bodyAngularVelocity_straightFlight (B : RigidBody 3) :
    (straightFlight B).bodyAngularVelocity = 0 :=
  RigidBodyMotion.bodyAngularVelocity_of_orientation_const _ 1 rfl

/-- A nonzero straight-flight trajectory: the position rate is `(1, 0, 0) ≠ 0`, but the reduced
state, the body velocity `(1, 0, 0)` and the body angular velocity `0`, has zero rate, and the plant
holds with unit mass, gravity `(0, 0, -1)` and the lift maps, so its residual vanishes. -/
lemma straightFlight_fixture (B : RigidBody 3) (t : Time) :
    ∂ₜ straightPosition t = ![1, 0, 0] ∧
      bodyVelocity (straightFlight B) straightPosition t = ![1, 0, 0] ∧
      ∂ₜ (bodyVelocity (straightFlight B) straightPosition) t = 0 ∧
      (straightFlight B).bodyAngularVelocity t = 0 ∧
      SixDofPlant liftMaps (bodyVelocity (straightFlight B) straightPosition) (straightFlight B)
        straightPosition 1 ![0, 0, -1] t := by
  have hv := bodyVelocity_straightFlight B
  have hω := bodyAngularVelocity_straightFlight B
  have hdv : ∂ₜ (bodyVelocity (straightFlight B) straightPosition) t = 0 := by
    rw [hv]
    exact Time.deriv_const _
  have hdω : ∂ₜ (straightFlight B).bodyAngularVelocity t = 0 := by
    rw [hω]
    exact Time.deriv_const (0 : Fin 3 → ℝ)
  refine ⟨deriv_straightPosition t, by rw [hv], hdv, by rw [hω]; rfl, ?_⟩
  have hdom : bodyVelocity (straightFlight B) straightPosition t ∈ liftMaps.domain := by
    rw [hv]
    change (0 : ℝ) < ![(1 : ℝ), 0, 0] 0
    norm_num
  refine ⟨hdom, ?_, ?_⟩
  · have hF : liftMaps.force ⟨_, hdom⟩ = ![0, 0, 1] := rfl
    rw [hF, hdv, hv, hω]
    ext i
    fin_cases i <;> simp [inertialToBodyVec, straightFlight]
  · have hM : liftMaps.moment ⟨_, hdom⟩ = 0 := rfl
    rw [hM, hdω, hω]
    simp

/-- For a mass distribution with centre of mass `0`, straight flight satisfies both inertial
balance laws: no net force (`0 = (0, 0, 1) + (0, 0, -1)`) and no torque. -/
lemma straightFlight_balanceLaws (B : RigidBody 3) (hc : B.centerOfMass = 0) (t : Time) :
    (1 : ℝ) • ∂ₜ (∂ₜ straightPosition) t =
        bodyToInertialVec ((straightFlight B).orientation t) ![0, 0, 1] + (1 : ℝ) • ![0, 0, -1] ∧
      ∂ₜ (comAngularMomentum (straightFlight B)) t =
        bodyToInertialVec ((straightFlight B).orientation t) 0 := by
  obtain ⟨_, hbody⟩ := (straightFlight_fixture B t).2.2.2.2
  exact (balanceLaws_iff_sixDofBodyEquations (straightFlight B) straightPosition isOpen_univ
    (contDiffOn_straightFlight_orientation B) contDiffOn_straightPosition hc one_pos _ _ _
    (Set.mem_univ t)).mpr hbody

/-- No out-of-domain evaluation: at a state without positive forward body velocity the lift maps
are not admitted, and the plant fails whatever the motion, mass and gravity. -/
lemma liftMaps_not_sixDofPlant (M : RigidBodyMotion 3) (X : Time → Fin 3 → ℝ) (m : ℝ)
    (g : Fin 3 → ℝ) {t : Time} (h : bodyVelocity M X t 0 ≤ 0) :
    ¬ SixDofPlant liftMaps (bodyVelocity M X) M X m g t := by
  rintro ⟨hx, -⟩
  exact absurd hx (not_lt.mpr h)

/-! ## B. Consumers of the public lemmas -/

-- The body velocity of straight flight is differentiable, as for any `C²` position and orientation.
example (B : RigidBody 3) (t : Time) :
    DifferentiableAt ℝ (bodyVelocity (straightFlight B) straightPosition) t :=
  differentiableAt_bodyVelocity _ _ isOpen_univ (contDiffOn_straightFlight_orientation B)
    contDiffOn_straightPosition (Set.mem_univ t)

-- The coefficient-map wrapper on straight flight: for a mass distribution with centre of mass `0`,
-- the plant gives an admitted state and both inertial laws with the lift and the zero moment that
-- the lift maps give there.
example (B : RigidBody 3) (hc : B.centerOfMass = 0) (t : Time) :
    ∃ hx : bodyVelocity (straightFlight B) straightPosition t ∈ liftMaps.domain,
      (1 : ℝ) • ∂ₜ (∂ₜ straightPosition) t =
          bodyToInertialVec ((straightFlight B).orientation t)
              (liftMaps.force ⟨bodyVelocity (straightFlight B) straightPosition t, hx⟩) +
            (1 : ℝ) • ![0, 0, -1] ∧
        ∂ₜ (comAngularMomentum (straightFlight B)) t =
          bodyToInertialVec ((straightFlight B).orientation t)
            (liftMaps.moment ⟨bodyVelocity (straightFlight B) straightPosition t, hx⟩) :=
  (sixDofPlant_iff liftMaps _ (straightFlight B) straightPosition isOpen_univ
    (contDiffOn_straightFlight_orientation B) contDiffOn_straightPosition hc one_pos _
    (Set.mem_univ t)).mp (straightFlight_fixture B t).2.2.2.2

/-! ## C. A steady level turn -/

/-- A steady level turn of the mass distribution `B` at unit speed and unit yaw rate: the
orientation `Rz(t)` of the constructed rotation about the third axis with initial rate `1` and no
angular acceleration, and the centre of mass on the circle of radius `1` about `(0, 1, 0)`. -/
private noncomputable def steadyTurn (B : RigidBody 3) : RigidBodyMotion 3 where
  toRigidBody := B
  comTrajectory := fun s => ⟨![Real.sin s.val, 1 - Real.cos s.val, 0]⟩
  orientation := (fixedAxisMotion B 1 0).orientation

/-- The inertial position `(sin s, 1 - cos s, 0)` of the steady turn at time `s`. -/
private noncomputable def turnPosition (s : Time) : Fin 3 → ℝ :=
  ![Real.sin s.val, 1 - Real.cos s.val, 0]

/-- The orientation of the steady turn is the rotation by the angle `t` about the third axis. -/
private lemma steadyTurn_orientation (B : RigidBody 3) (t : Time) :
    (((steadyTurn B).orientation t : Matrix (Fin 3) (Fin 3) ℝ)) = rotZ t.val := by
  change rotZ (fixedAxisAngle 1 0 t) = rotZ t.val
  simp [fixedAxisAngle]

/-- The steady turn has the body angular velocity `(0, 0, 1)`. -/
private lemma steadyTurn_bodyAngularVelocity (B : RigidBody 3) (t : Time) :
    (steadyTurn B).bodyAngularVelocity t = ![0, 0, 1] := by
  change (fixedAxisMotion B 1 0).bodyAngularVelocity t = _
  rw [fixedAxisMotion_bodyAngularVelocity, (deriv_fixedAxisAngle 1 0 t).1]
  simp

/-- The orientation of the steady turn is `C²` entry by entry. -/
private lemma contDiffOn_steadyTurn_orientation (B : RigidBody 3) (i j : Fin 3) :
    ContDiffOn ℝ 2 (fun s => ((steadyTurn B).orientation s).1 i j) Set.univ :=
  (contDiff_infty.1 (contDiff_fixedAxisMotion_orientation_apply B 1 0 i j) 2).contDiffOn

/-- The position of the steady turn is smooth. -/
private lemma contDiffOn_turnPosition : ContDiffOn ℝ 2 turnPosition Set.univ := by
  refine (contDiff_pi.2 fun i => ?_).contDiffOn
  fin_cases i
  · exact Real.contDiff_sin.comp Time.toRealCLM.contDiff
  · exact contDiff_const.sub (Real.contDiff_cos.comp Time.toRealCLM.contDiff)
  · exact contDiff_const

/-- The position of the steady turn has rate `(cos t, sin t, 0)`. -/
private lemma deriv_turnPosition (t : Time) :
    ∂ₜ turnPosition t = ![Real.cos t.val, Real.sin t.val, 0] := by
  have hγ : HasDerivAt (fun x : ℝ => ![Real.sin x, 1 - Real.cos x, 0])
      ![Real.cos (Time.toRealCLE t), Real.sin (Time.toRealCLE t), 0] (Time.toRealCLE t) := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using Real.hasDerivAt_sin (Time.toRealCLE t)
    · simpa using (Real.hasDerivAt_cos (Time.toRealCLE t)).const_sub 1
    · simpa using hasDerivAt_const (Time.toRealCLE t) (0 : ℝ)
  have h : turnPosition =
      fun s => (fun x : ℝ => ![Real.sin x, 1 - Real.cos x, 0]) (Time.toRealCLE s) := rfl
  rw [h]
  exact Time.deriv_comp_toRealCLE_of_hasDerivAt _ t _ hγ

/-- The position of the steady turn has the acceleration `(-sin t, cos t, 0)`, toward the centre
`(0, 1, 0)`. -/
private lemma deriv_deriv_turnPosition (t : Time) :
    ∂ₜ (∂ₜ turnPosition) t = ![-Real.sin t.val, Real.cos t.val, 0] := by
  have hγ : HasDerivAt (fun x : ℝ => ![Real.cos x, Real.sin x, 0])
      ![-Real.sin (Time.toRealCLE t), Real.cos (Time.toRealCLE t), 0] (Time.toRealCLE t) := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using Real.hasDerivAt_cos (Time.toRealCLE t)
    · simpa using Real.hasDerivAt_sin (Time.toRealCLE t)
    · simpa using hasDerivAt_const (Time.toRealCLE t) (0 : ℝ)
  have h : ∂ₜ turnPosition =
      fun s => (fun x : ℝ => ![Real.cos x, Real.sin x, 0]) (Time.toRealCLE s) := by
    funext s
    exact deriv_turnPosition s
  rw [h]
  exact Time.deriv_comp_toRealCLE_of_hasDerivAt _ t _ hγ

/-- The steady turn has the constant body velocity `(1, 0, 0)`. -/
private lemma bodyVelocity_steadyTurn (B : RigidBody 3) :
    bodyVelocity (steadyTurn B) turnPosition = fun _ => ![1, 0, 0] := by
  funext s
  have hcs := Real.cos_sq_add_sin_sq s.val
  simp only [bodyVelocity, deriv_turnPosition, inertialToBodyVec, steadyTurn_orientation]
  ext i
  fin_cases i <;> simp [rotZ, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · linear_combination hcs
  · ring

/-- The vertical gravity `(0, 0, -1)` has the same components in the body axes of the steady turn,
since the rotation about the third axis fixes it. -/
private lemma steadyTurn_gravity (B : RigidBody 3) (t : Time) :
    inertialToBodyVec ((steadyTurn B).orientation t) ![0, 0, -1] = ![0, 0, -1] := by
  simp only [inertialToBodyVec, steadyTurn_orientation]
  ext i
  fin_cases i <;> simp [rotZ, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

-- The steady turn: the body velocity is the constant `(1, 0, 0)`, the body angular velocity is
-- `(0, 0, 1)`, a turn to the left, and the gyroscopic term `ω_B × v_B` is `(0, 1, 0)`, toward the
-- centre of the turn.
example (B : RigidBody 3) (t : Time) :
    bodyVelocity (steadyTurn B) turnPosition t = ![1, 0, 0] ∧
      ∂ₜ (bodyVelocity (steadyTurn B) turnPosition) t = 0 ∧
      (steadyTurn B).bodyAngularVelocity t = ![0, 0, 1] ∧
      (steadyTurn B).bodyAngularVelocity t ⨯₃ bodyVelocity (steadyTurn B) turnPosition t =
        ![0, 1, 0] := by
  have hv := bodyVelocity_steadyTurn B
  refine ⟨by rw [hv], by rw [hv]; exact Time.deriv_const _, steadyTurn_bodyAngularVelocity B t,
    ?_⟩
  rw [hv, steadyTurn_bodyAngularVelocity]
  ext i
  fin_cases i <;> simp [cross_apply]

-- The inertial law of the steady turn with unit mass, gravity `(0, 0, -1)` and the body force
-- `(0, 1, 1)`, checked by differentiating the position directly:
-- `X'' = (-sin t, cos t, 0) = R (0, 1, 1) + (0, 0, -1)`. The translational correspondence turns it
-- into the body equation, whose right side `(0, 1, 1) + (0, 0, -1) - (0, 1, 0)` is the zero rate of
-- the constant body velocity.
example (B : RigidBody 3) (t : Time) :
    (1 : ℝ) • ∂ₜ (∂ₜ turnPosition) t =
        bodyToInertialVec ((steadyTurn B).orientation t) ![0, 1, 1] + (1 : ℝ) • ![0, 0, -1] ∧
      ∂ₜ (bodyVelocity (steadyTurn B) turnPosition) t =
        (1 : ℝ)⁻¹ • ![0, 1, 1] + inertialToBodyVec ((steadyTurn B).orientation t) ![0, 0, -1] -
          (steadyTurn B).bodyAngularVelocity t ⨯₃ bodyVelocity (steadyTurn B) turnPosition t ∧
      ∂ₜ (bodyVelocity (steadyTurn B) turnPosition) t = 0 := by
  have hlaw : (1 : ℝ) • ∂ₜ (∂ₜ turnPosition) t =
      bodyToInertialVec ((steadyTurn B).orientation t) ![0, 1, 1] + (1 : ℝ) • ![0, 0, -1] := by
    rw [deriv_deriv_turnPosition]
    simp only [bodyToInertialVec, steadyTurn_orientation]
    ext i
    fin_cases i <;> simp [rotZ]
  refine ⟨hlaw, (newton_iff_deriv_bodyVelocity (steadyTurn B) turnPosition isOpen_univ
    (contDiffOn_steadyTurn_orientation B) contDiffOn_turnPosition one_pos _ _
    (Set.mem_univ t)).mp hlaw, ?_⟩
  rw [bodyVelocity_steadyTurn]
  exact Time.deriv_const _

-- The side force must point to the centre of the turn: with the body force `(0, -1, 1)` the
-- inertial law fails, since the body equation would need `v_B' = (0, -2, 0)` while the body
-- velocity is constant.
example (B : RigidBody 3) (t : Time) :
    ¬ (1 : ℝ) • ∂ₜ (∂ₜ turnPosition) t =
        bodyToInertialVec ((steadyTurn B).orientation t) ![0, -1, 1] + (1 : ℝ) • ![0, 0, -1] := by
  rw [newton_iff_deriv_bodyVelocity (steadyTurn B) turnPosition isOpen_univ
    (contDiffOn_steadyTurn_orientation B) contDiffOn_turnPosition one_pos _ _ (Set.mem_univ t),
    bodyVelocity_steadyTurn, Time.deriv_const, steadyTurn_bodyAngularVelocity, steadyTurn_gravity]
  intro h
  have h1 := congrFun h 1
  norm_num [cross_apply] at h1

end PhyslibExtTest.Mechanics.FlightPlant
