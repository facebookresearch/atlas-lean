/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.FlightPlant
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Tests for `PhyslibExt.Mechanics.FlightPlant`

Consumers of the translational correspondence, of the six-degree-of-freedom package and of the
coefficient-map wrapper: straight flight, the admitted domain of a lift map, a unit point mass,
a steady level turn, the controlled longitudinal fixture and its linearization about the trim.

## i. Overview

Straight flight of a mass distribution of mass `m > 0`, with identity orientation and centre of
mass at `(t, 0, 0)`, has the nonzero position rate `(1, 0, 0)`, but its reduced state, the body
velocity `(1, 0, 0)` and the body angular velocity `0`, has zero rate: with gravity `(0, 0, -1)`
and a lift map giving the body force `(0, 0, m)` and no moment, the plant holds and its residual
vanishes. The lift maps are admitted only at states with positive forward body velocity, and the
plant fails elsewhere. A massless motion is never a plant, and a plant's body velocity is
differentiable, so the rate in its translational equation is a genuine derivative. A unit point mass
at the origin has positive mass and centre of mass `0`, so the hypotheses of the package are
satisfiable.

A steady level turn at unit speed and unit yaw rate, with orientation `Rz(t)` and centre of mass on
the circle `(sin t, 1 - cos t, 0)` of radius `1` about `(0, 1, 0)`, has the constant body velocity
`(1, 0, 0)`, the body angular velocity `(0, 0, 1)` and the gyroscopic term `ω_B × v_B = (0, 1, 0)`,
toward the centre of the turn. For a mass distribution of positive mass `m`, differentiating the
trajectory directly gives `m X'' = m (-sin t, cos t, 0) = R (m (0, 1, 1)) + m (0, 0, -1)`, the
inertial law with the body force `m (0, 1, 1)`, and the translational correspondence turns it into
the body equation; with the body force `m (0, -1, 1)`, away from the centre, the law fails.

The controlled longitudinal fixture: at the trim the lift `(0, 1, 0)` balances the unit weight,
the drag `(-3/20, 0, 0)` is balanced by the actuator thrust `(3/20, 0, 0)` and the reduced field
vanishes. Four point masses `1/4` at `(±1, 0, 0)` and `(0, ±1, 0)` have mass `1`, centre of mass
`0` and unit pitch inertia, so the restriction lemma applies: a planar plant solution obeys
`q' = -2 q - sin θ`, and the trim from `(3, 5)` is a plant solution whose centre of mass moves.
The actuators stay within their bounds at a corner of the box, and a state of zero speed is
rejected.

The linearization about the trim: the pitch-restoring entry `-1` of the Jacobian, read off its
block form; the derivative at the trim in the pitch direction, `(0, 0, 0, -1)`; the field at
`x = 1/100` as its linear part plus the cubic term `-1/1000000`. At `δ = (1/100, -1/100, 1/100,
1/100)` the remainder has the cubic term `-1/1000000`, attaining the bound `r ‖δ‖²` with
`r = 1/100`, and a positive `θ - sin θ` within `(r / 6) ‖δ‖²`; the first-order remainder of the
uncertainty-propagation API is the same cubic term, and the componentwise Hessian theorem bounds it
by `3/1000000`. The reduced field is differentiable; its second derivatives are `-6/100` for the
forward component at `x = 1/100` and `0` for the pitch component at the trim, where the Hessian of
the forward component vanishes. The all-ones state has Euclidean norm at most `2`, a state of
Euclidean norm at most `1/100` is admitted, and there the pitch remainder is at most `‖e‖² / 600`.
The quarter-mass trim moves forward with rate at least `99/100`.

## ii. Key results

- `straightFlight`, `liftMaps`, `straightFlight_fixture`, `straightFlight_balanceLaws`,
  `liftMaps_not_sixDofPlant` : the straight-flight fixture.
- `trim_fixture` : the trim of the controlled longitudinal fixture.
- `longitudinalRemainder_fixture` : the nonlinear remainder at a nonzero state.

## iii. Table of contents

- A. Straight flight
- B. Consumers of the public lemmas
- C. A steady level turn
- D. The controlled longitudinal fixture
- E. Linearization about the trim

## iv. References

- `PhyslibExt.Mechanics.FlightPlant`, `PhyslibExt.Mechanics.RigidMotionPorts` and
  `PhyslibExt.Statistics.UncertaintyPropagation`.
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

/-- Lift maps for the mass `m` in the gravity `(0, 0, -1)`: the body force `(0, 0, m)`, which
balances the weight, and no moment, admitted at the states (body velocities) with positive forward
component. -/
def liftMaps (m : ℝ) : ForceMomentMaps (Fin 3 → ℝ) where
  domain := {v | 0 < v 0}
  force := fun _ => ![0, 0, m]
  moment := fun _ => 0

/-- The orientation of straight flight is constant, hence `C²` entry by entry. -/
private lemma contDiffOn_straightFlight_orientation (B : RigidBody 3) (i j : Fin 3) :
    ContDiffOn ℝ 2 (fun s => ((straightFlight B).orientation s).1 i j) Set.univ :=
  contDiffOn_const

/-- The centre-of-mass trajectory of straight flight is smooth, component by component. -/
private lemma contDiffOn_straightFlight_comTrajectory (B : RigidBody 3) (j : Fin 3) :
    ContDiffOn ℝ 2 (fun s => (straightFlight B).comTrajectory s j) Set.univ := by
  refine ContDiff.contDiffOn ?_
  fin_cases j
  · exact Time.toRealCLM.contDiff
  · exact contDiff_const
  · exact contDiff_const

/-- The centre of mass of straight flight moves with the velocity `(1, 0, 0)`. -/
private lemma deriv_straightFlight_comTrajectory (B : RigidBody 3) (t : Time) :
    ∂ₜ (fun s j => (straightFlight B).comTrajectory s j) t = ![1, 0, 0] := by
  have hγ : HasDerivAt (fun x : ℝ => ![x, 0, 0]) ![1, 0, 0] (Time.toRealCLE t) := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hasDerivAt_id' (Time.toRealCLE t)
    · simpa using hasDerivAt_const (Time.toRealCLE t) (0 : ℝ)
    · simpa using hasDerivAt_const (Time.toRealCLE t) (0 : ℝ)
  have h : (fun s j => (straightFlight B).comTrajectory s j) =
      fun s => (fun x : ℝ => ![x, 0, 0]) (Time.toRealCLE s) := rfl
  rw [h]
  exact Time.deriv_comp_toRealCLE_of_hasDerivAt _ t _ hγ

/-- The body velocity of straight flight is constant, `(1, 0, 0)`. -/
private lemma bodyVelocity_straightFlight (B : RigidBody 3) :
    bodyVelocity (straightFlight B) = fun _ => ![1, 0, 0] := by
  funext s
  rw [bodyVelocity, deriv_straightFlight_comTrajectory]
  change (1 : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *ᵥ _ = _
  simp

/-- Straight flight does not turn. -/
private lemma bodyAngularVelocity_straightFlight (B : RigidBody 3) :
    (straightFlight B).bodyAngularVelocity = 0 :=
  RigidBodyMotion.bodyAngularVelocity_of_orientation_const _ 1 rfl

/-- A nonzero straight-flight trajectory: for a mass distribution of positive mass `m`, the
position rate of the centre of mass is `(1, 0, 0) ≠ 0`, but the reduced state, the body velocity
`(1, 0, 0)` and the body angular velocity `0`, has zero rate, and the plant holds with gravity
`(0, 0, -1)` and the lift maps of the mass `m`, so its residual vanishes. -/
lemma straightFlight_fixture (B : RigidBody 3) (hm : 0 < B.mass) (t : Time) :
    ∂ₜ (fun s j => (straightFlight B).comTrajectory s j) t = ![1, 0, 0] ∧
      bodyVelocity (straightFlight B) t = ![1, 0, 0] ∧
      ∂ₜ (bodyVelocity (straightFlight B)) t = 0 ∧
      (straightFlight B).bodyAngularVelocity t = 0 ∧
      SixDofPlant (liftMaps B.mass) (bodyVelocity (straightFlight B)) (straightFlight B)
        ![0, 0, -1] t := by
  have hv := bodyVelocity_straightFlight B
  have hω := bodyAngularVelocity_straightFlight B
  have hdv : ∂ₜ (bodyVelocity (straightFlight B)) t = 0 := by
    rw [hv]
    exact Time.deriv_const _
  have hdω : ∂ₜ (straightFlight B).bodyAngularVelocity t = 0 := by
    rw [hω]
    exact Time.deriv_const (0 : Fin 3 → ℝ)
  refine ⟨deriv_straightFlight_comTrajectory B t, by rw [hv], hdv, by rw [hω]; rfl, ?_⟩
  have hdom : bodyVelocity (straightFlight B) t ∈ (liftMaps B.mass).domain := by
    rw [hv]
    change (0 : ℝ) < ![(1 : ℝ), 0, 0] 0
    norm_num
  refine ⟨hm, ⟨Set.univ, isOpen_univ, Set.mem_univ t, contDiffOn_straightFlight_orientation B,
    contDiffOn_straightFlight_comTrajectory B⟩, hdom, ?_, ?_⟩
  · have hF : (liftMaps B.mass).force ⟨_, hdom⟩ = ![0, 0, B.mass] := rfl
    rw [hF, hdv, hv, hω]
    ext i
    fin_cases i <;> simp [inertialToBodyVec, straightFlight, hm.ne']
  · have hM : (liftMaps B.mass).moment ⟨_, hdom⟩ = 0 := rfl
    rw [hM, hdω, hω]
    simp

/-- For a mass distribution of positive mass `m` with centre of mass `0`, straight flight satisfies
both inertial balance laws: no net force (`0 = (0, 0, m) + m (0, 0, -1)`) and no torque. -/
lemma straightFlight_balanceLaws (B : RigidBody 3) (hc : B.centerOfMass = 0) (hm : 0 < B.mass)
    (t : Time) :
    B.mass • ∂ₜ (∂ₜ (fun s j => (straightFlight B).comTrajectory s j)) t =
        bodyToInertialVec ((straightFlight B).orientation t) ![0, 0, B.mass] +
          B.mass • ![0, 0, -1] ∧
      ∂ₜ (comAngularMomentum (straightFlight B)) t =
        bodyToInertialVec ((straightFlight B).orientation t) 0 := by
  obtain ⟨-, -, _, hbody⟩ := (straightFlight_fixture B hm t).2.2.2.2
  exact (balanceLaws_iff_sixDofBodyEquations (straightFlight B) isOpen_univ
    (contDiffOn_straightFlight_orientation B) (contDiffOn_straightFlight_comTrajectory B) hc hm
    _ _ _ (Set.mem_univ t)).mpr hbody

/-- No out-of-domain evaluation: at a state without positive forward body velocity the lift maps
are not admitted, and the plant fails whatever the motion, the mass the maps are built for and the
gravity. -/
lemma liftMaps_not_sixDofPlant (M : RigidBodyMotion 3) (m : ℝ) (g : Fin 3 → ℝ) {t : Time}
    (h : bodyVelocity M t 0 ≤ 0) : ¬ SixDofPlant (liftMaps m) (bodyVelocity M) M g t := by
  rintro ⟨-, -, hx, -⟩
  exact absurd hx (not_lt.mpr h)

/-! ## B. Consumers of the public lemmas -/

-- The body velocity of straight flight is differentiable, as along any `C²` motion.
example (B : RigidBody 3) (t : Time) : DifferentiableAt ℝ (bodyVelocity (straightFlight B)) t :=
  differentiableAt_bodyVelocity _ isOpen_univ (contDiffOn_straightFlight_orientation B)
    (contDiffOn_straightFlight_comTrajectory B) (Set.mem_univ t)

-- The coefficient-map wrapper on straight flight: for a mass distribution of positive mass `m` with
-- centre of mass `0`, the plant gives an admitted state and both inertial laws with the lift
-- `(0, 0, m)` and the zero moment that the lift maps give there.
example (B : RigidBody 3) (hc : B.centerOfMass = 0) (hm : 0 < B.mass) (t : Time) :
    ∃ hx : bodyVelocity (straightFlight B) t ∈ (liftMaps B.mass).domain,
      B.mass • ∂ₜ (∂ₜ (fun s j => (straightFlight B).comTrajectory s j)) t =
          bodyToInertialVec ((straightFlight B).orientation t)
              ((liftMaps B.mass).force ⟨bodyVelocity (straightFlight B) t, hx⟩) +
            B.mass • ![0, 0, -1] ∧
        ∂ₜ (comAngularMomentum (straightFlight B)) t =
          bodyToInertialVec ((straightFlight B).orientation t)
            ((liftMaps B.mass).moment ⟨bodyVelocity (straightFlight B) t, hx⟩) :=
  ((sixDofPlant_iff (liftMaps B.mass) _ (straightFlight B) hc _ t).mp
    (straightFlight_fixture B hm t).2.2.2.2).2.2

-- A massless motion is never a plant: at `M.mass = 0` the totalized inverse `M.mass⁻¹ = 0` would
-- drop the force from the translational equation, and the plant excludes that case.
example {S : Type*} (c : ForceMomentMaps S) (x : Time → S) (M : RigidBodyMotion 3)
    (g : Fin 3 → ℝ) (t : Time) (h0 : M.mass = 0) : ¬ SixDofPlant c x M g t := by
  rintro ⟨hm, -⟩
  rw [h0] at hm
  exact lt_irrefl 0 hm

-- A plant's body velocity is differentiable at `t`, so `∂ₜ` of it in the translational equation is
-- a genuine derivative, not a fallback value.
example {S : Type*} (c : ForceMomentMaps S) (x : Time → S) (M : RigidBodyMotion 3)
    (g : Fin 3 → ℝ) (t : Time) (h : SixDofPlant c x M g t) :
    DifferentiableAt ℝ (bodyVelocity M) t := by
  obtain ⟨-, ⟨U, hU, ht, hR, hX⟩, -⟩ := h
  exact differentiableAt_bodyVelocity M hU hR hX ht

/-- A unit point mass at the origin of body coordinates. -/
private noncomputable def unitPointMass : RigidBody 3 where
  ρ :=
    { toFun := fun f => f 0
      map_add' := fun f g => by simp only [ContMDiffMap.coe_add, Pi.add_apply]
      map_smul' := fun r f => by
        simp only [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }

/-- The unit point mass has mass `1`. -/
private lemma unitPointMass_mass : unitPointMass.mass = 1 := rfl

/-- The unit point mass has its centre of mass at the origin. -/
private lemma unitPointMass_centerOfMass : unitPointMass.centerOfMass = 0 := by
  ext i
  fin_cases i <;> simp [RigidBody.centerOfMass, unitPointMass, Space.zero_apply]

-- The hypotheses of the package are satisfiable: the unit point mass has positive mass and centre
-- of mass `0`, and in straight flight it satisfies both inertial balance laws, with the lift
-- `(0, 0, 1)` against the gravity `(0, 0, -1)`.
example (t : Time) :
    0 < unitPointMass.mass ∧ unitPointMass.centerOfMass = 0 ∧
      ∂ₜ (∂ₜ (fun s j => (straightFlight unitPointMass).comTrajectory s j)) t =
        bodyToInertialVec ((straightFlight unitPointMass).orientation t) ![0, 0, 1] + ![0, 0, -1] ∧
      ∂ₜ (comAngularMomentum (straightFlight unitPointMass)) t = 0 := by
  have hm : 0 < unitPointMass.mass := by
    rw [unitPointMass_mass]
    norm_num
  obtain ⟨h1, h2⟩ := straightFlight_balanceLaws unitPointMass unitPointMass_centerOfMass hm t
  rw [unitPointMass_mass, one_smul, one_smul] at h1
  refine ⟨hm, unitPointMass_centerOfMass, h1, ?_⟩
  rw [h2]
  simp [bodyToInertialVec]

/-! ## C. A steady level turn -/

/-- A steady level turn of the mass distribution `B` at unit speed and unit yaw rate: the
orientation `Rz(t)` of the constructed rotation about the third axis with initial rate `1` and no
angular acceleration, and the centre of mass on the circle of radius `1` about `(0, 1, 0)`. -/
private noncomputable def steadyTurn (B : RigidBody 3) : RigidBodyMotion 3 where
  toRigidBody := B
  comTrajectory := fun s => ⟨![Real.sin s.val, 1 - Real.cos s.val, 0]⟩
  orientation := (fixedAxisMotion B 1 0).orientation

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

/-- The centre-of-mass trajectory of the steady turn is smooth, component by component. -/
private lemma contDiffOn_steadyTurn_comTrajectory (B : RigidBody 3) (j : Fin 3) :
    ContDiffOn ℝ 2 (fun s => (steadyTurn B).comTrajectory s j) Set.univ := by
  refine ContDiff.contDiffOn ?_
  fin_cases j
  · exact Real.contDiff_sin.comp Time.toRealCLM.contDiff
  · exact contDiff_const.sub (Real.contDiff_cos.comp Time.toRealCLM.contDiff)
  · exact contDiff_const

/-- The centre of mass of the steady turn moves with the velocity `(cos t, sin t, 0)`. -/
private lemma deriv_steadyTurn_comTrajectory (B : RigidBody 3) (t : Time) :
    ∂ₜ (fun s j => (steadyTurn B).comTrajectory s j) t = ![Real.cos t.val, Real.sin t.val, 0] := by
  have hγ : HasDerivAt (fun x : ℝ => ![Real.sin x, 1 - Real.cos x, 0])
      ![Real.cos (Time.toRealCLE t), Real.sin (Time.toRealCLE t), 0] (Time.toRealCLE t) := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using Real.hasDerivAt_sin (Time.toRealCLE t)
    · simpa using (Real.hasDerivAt_cos (Time.toRealCLE t)).const_sub 1
    · simpa using hasDerivAt_const (Time.toRealCLE t) (0 : ℝ)
  have h : (fun s j => (steadyTurn B).comTrajectory s j) =
      fun s => (fun x : ℝ => ![Real.sin x, 1 - Real.cos x, 0]) (Time.toRealCLE s) := rfl
  rw [h]
  exact Time.deriv_comp_toRealCLE_of_hasDerivAt _ t _ hγ

/-- The centre of mass of the steady turn has the acceleration `(-sin t, cos t, 0)`, toward the
centre `(0, 1, 0)`. -/
private lemma deriv_deriv_steadyTurn_comTrajectory (B : RigidBody 3) (t : Time) :
    ∂ₜ (∂ₜ (fun s j => (steadyTurn B).comTrajectory s j)) t =
      ![-Real.sin t.val, Real.cos t.val, 0] := by
  have hγ : HasDerivAt (fun x : ℝ => ![Real.cos x, Real.sin x, 0])
      ![-Real.sin (Time.toRealCLE t), Real.cos (Time.toRealCLE t), 0] (Time.toRealCLE t) := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using Real.hasDerivAt_cos (Time.toRealCLE t)
    · simpa using Real.hasDerivAt_sin (Time.toRealCLE t)
    · simpa using hasDerivAt_const (Time.toRealCLE t) (0 : ℝ)
  have h : ∂ₜ (fun s j => (steadyTurn B).comTrajectory s j) =
      fun s => (fun x : ℝ => ![Real.cos x, Real.sin x, 0]) (Time.toRealCLE s) := by
    funext s
    exact deriv_steadyTurn_comTrajectory B s
  rw [h]
  exact Time.deriv_comp_toRealCLE_of_hasDerivAt _ t _ hγ

/-- The steady turn has the constant body velocity `(1, 0, 0)`. -/
private lemma bodyVelocity_steadyTurn (B : RigidBody 3) :
    bodyVelocity (steadyTurn B) = fun _ => ![1, 0, 0] := by
  funext s
  have hcs := Real.cos_sq_add_sin_sq s.val
  simp only [bodyVelocity, deriv_steadyTurn_comTrajectory, inertialToBodyVec,
    steadyTurn_orientation]
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
    bodyVelocity (steadyTurn B) t = ![1, 0, 0] ∧ ∂ₜ (bodyVelocity (steadyTurn B)) t = 0 ∧
      (steadyTurn B).bodyAngularVelocity t = ![0, 0, 1] ∧
      (steadyTurn B).bodyAngularVelocity t ⨯₃ bodyVelocity (steadyTurn B) t = ![0, 1, 0] := by
  have hv := bodyVelocity_steadyTurn B
  refine ⟨by rw [hv], by rw [hv]; exact Time.deriv_const _, steadyTurn_bodyAngularVelocity B t,
    ?_⟩
  rw [hv, steadyTurn_bodyAngularVelocity]
  ext i
  fin_cases i <;> simp [cross_apply]

-- The inertial law of the steady turn of a mass distribution of positive mass `m`, with gravity
-- `(0, 0, -1)` and the body force `m (0, 1, 1)`, checked by differentiating the trajectory
-- directly: `m X'' = m (-sin t, cos t, 0) = R (m (0, 1, 1)) + m (0, 0, -1)`. The translational
-- correspondence turns it into the body equation, whose right side
-- `(0, 1, 1) + (0, 0, -1) - (0, 1, 0)` is the zero rate of the constant body velocity.
example (B : RigidBody 3) (hm : 0 < B.mass) (t : Time) :
    B.mass • ∂ₜ (∂ₜ (fun s j => (steadyTurn B).comTrajectory s j)) t =
        bodyToInertialVec ((steadyTurn B).orientation t) (B.mass • ![0, 1, 1]) +
          B.mass • ![0, 0, -1] ∧
      ∂ₜ (bodyVelocity (steadyTurn B)) t =
        B.mass⁻¹ • (B.mass • ![0, 1, 1]) +
            inertialToBodyVec ((steadyTurn B).orientation t) ![0, 0, -1] -
          (steadyTurn B).bodyAngularVelocity t ⨯₃ bodyVelocity (steadyTurn B) t ∧
      ∂ₜ (bodyVelocity (steadyTurn B)) t = 0 := by
  have hlaw : B.mass • ∂ₜ (∂ₜ (fun s j => (steadyTurn B).comTrajectory s j)) t =
      bodyToInertialVec ((steadyTurn B).orientation t) (B.mass • ![0, 1, 1]) +
        B.mass • ![0, 0, -1] := by
    rw [deriv_deriv_steadyTurn_comTrajectory]
    simp only [bodyToInertialVec, steadyTurn_orientation]
    ext i
    fin_cases i <;> simp [rotZ]
  refine ⟨hlaw, (newton_iff_deriv_bodyVelocity (steadyTurn B) isOpen_univ
    (contDiffOn_steadyTurn_orientation B) (contDiffOn_steadyTurn_comTrajectory B) hm _ _
    (Set.mem_univ t)).mp hlaw, ?_⟩
  rw [bodyVelocity_steadyTurn]
  exact Time.deriv_const _

-- The side force must point to the centre of the turn: for positive mass `m`, the body force
-- `m (0, -1, 1)` fails the inertial law, since the body equation would need `v_B' = (0, -2, 0)`
-- while the body velocity is constant.
example (B : RigidBody 3) (hm : 0 < B.mass) (t : Time) :
    ¬ B.mass • ∂ₜ (∂ₜ (fun s j => (steadyTurn B).comTrajectory s j)) t =
        bodyToInertialVec ((steadyTurn B).orientation t) (B.mass • ![0, -1, 1]) +
          B.mass • ![0, 0, -1] := by
  intro hlaw
  have h := (newton_iff_deriv_bodyVelocity (steadyTurn B) isOpen_univ
    (contDiffOn_steadyTurn_orientation B) (contDiffOn_steadyTurn_comTrajectory B) hm _ _
    (Set.mem_univ t)).mp hlaw
  have hmass : (steadyTurn B).mass = B.mass := rfl
  rw [hmass, bodyVelocity_steadyTurn, Time.deriv_const, steadyTurn_bodyAngularVelocity,
    steadyTurn_gravity, smul_smul, inv_mul_cancel₀ hm.ne', one_smul] at h
  have h1 := congrFun h 1
  norm_num [cross_apply] at h1

/-! ## D. The controlled longitudinal fixture -/

/-- Four point masses `1/4` at `(±1, 0, 0)` and `(0, ±1, 0)`: mass `1`, centre of mass `0` and the
inertia `diag(1/2, 1/2, 1)`, unit pitch inertia about the principal third axis. -/
private noncomputable def quarterMassBody : RigidBody 3 where
  ρ :=
    { toFun := fun f => (f ⟨![1, 0, 0]⟩ + f ⟨![-1, 0, 0]⟩ + f ⟨![0, 1, 0]⟩ + f ⟨![0, -1, 0]⟩) / 4
      map_add' := fun f g => by
        simp only [ContMDiffMap.coe_add, Pi.add_apply]
        ring
      map_smul' := fun r f => by
        simp only [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

/-- The quarter-mass body has mass `1`. -/
private lemma quarterMassBody_mass : quarterMassBody.mass = 1 := by
  norm_num [RigidBody.mass, quarterMassBody]

/-- The quarter-mass body has its centre of mass at the origin. -/
private lemma quarterMassBody_centerOfMass : quarterMassBody.centerOfMass = 0 := by
  ext i
  fin_cases i <;> simp [RigidBody.centerOfMass, quarterMassBody]

/-- The inertia of the quarter-mass body about its centre of mass is `diag(1/2, 1/2, 1)`. -/
private lemma quarterMassBody_inertia :
    quarterMassBody.inertiaTensorAbout quarterMassBody.centerOfMass =
      Matrix.diagonal ![1 / 2, 1 / 2, 1] := by
  rw [quarterMassBody_centerOfMass, RigidBody.inertiaTensorAbout_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RigidBody.inertiaTensor, quarterMassBody, Fin.sum_univ_three] <;> norm_num

/-- **Trim.** At the zero state `V = 1`, the lift `(0, 1, 0)` balances the unit weight, the drag
is `(-3/20, 0, 0)`, the actuator is the horizontal thrust `(3/20, 0, 0)`, the pitch moment is
`0`, the reduced field vanishes, and the state is admitted. -/
lemma trim_fixture :
    flightSpeed 0 0 = 1 ∧ liftForce 0 0 = ![0, 1, 0] ∧ dragForce 0 0 = ![-(3 / 20), 0, 0] ∧
      actuatorForce 0 0 = ![3 / 20, 0, 0] ∧ pitchMoment 0 0 = 0 ∧ reducedField 0 = 0 ∧
      (0 : Fin 4 → ℝ) ∈ actuatorBox := by
  have hV : flightSpeed 0 0 = 1 := by simp [flightSpeed]
  have hD : dragCoeff = 3 / 10 := dragCoeff_eq
  refine ⟨hV, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [liftForce, hV, liftCoeff]
  · ext i
    fin_cases i <;> simp [dragForce, hV, hD]
    norm_num
  · ext i
    fin_cases i <;> simp [actuatorForce, aeroForce, liftForce, dragForce, hV, hD, liftCoeff]
    norm_num
  · simp [pitchMoment]
  · ext i
    fin_cases i <;> simp [reducedField]
  · intro i
    simp

-- At the nonzero state `(x, z) = (1/100, -1/100)` the lift is perpendicular to the velocity and the
-- drag is `-(3 V / 20)` times it.
example : liftForce (1 / 100) (-1 / 100) ⬝ᵥ ![1 + 1 / 100, -1 / 100, 0] = 0 ∧
    dragForce (1 / 100) (-1 / 100) =
      -(3 / 20 * flightSpeed (1 / 100) (-1 / 100)) • ![1 + 1 / 100, -1 / 100, 0] :=
  ⟨(liftForce_dragForce_spec (1 / 100) (-1 / 100)).1,
    (liftForce_dragForce_spec (1 / 100) (-1 / 100)).2.2.2.1⟩

-- At the fast state `x = 1/100`, `z = 0` the aerodynamic force, the actuator and the weight add up
-- to the decelerating force `(-1/100 - 1/1000000, 0, 0)`.
example : aeroForce (1 / 100) 0 + actuatorForce (1 / 100) 0 + ![0, -1, 0] =
    ![-(1 / 100) - 1 / 1000000, 0, 0] := by
  rw [aeroForce_add_actuatorForce_add_weight]
  ext i
  fin_cases i <;> norm_num

-- Along a planar plant solution of the quarter-mass body the pitch rate obeys the closed-loop law
-- `q' = -2 q - sin θ`.
example {X₁ X₂ θ : Time → ℝ} (hX₁ : ContDiff ℝ 2 X₁) (hX₂ : ContDiff ℝ 2 X₂)
    (hθ : ContDiff ℝ 2 θ) (t : Time)
    (h : SixDofPlant longitudinalMaps (planarState X₁ X₂ θ) (planarMotion quarterMassBody X₁ X₂ θ)
      ![0, -1, 0] t) :
    ∂ₜ (fun s => planarState X₁ X₂ θ s 3) t =
      -2 * planarState X₁ X₂ θ t 3 - Real.sin (planarState X₁ X₂ θ t 2) := by
  have h' := ((planar_sixDofPlant_iff quarterMassBody quarterMassBody_mass
    quarterMassBody_centerOfMass quarterMassBody_inertia hX₁ hX₂ hθ t).mp h).2
  simpa [reducedField] using congrFun h' 3

-- The trim of the quarter-mass body from `p₀ = (3, 5)` is a plant solution at every time, and its
-- centre of mass moves with the nonzero rate `(1, 0, 0)`.
example (t : Time) :
    SixDofPlant longitudinalMaps (planarState (fun s => 3 + s.val) (fun _ => 5) (fun _ => 0))
        (planarMotion quarterMassBody (fun s => 3 + s.val) (fun _ => 5) (fun _ => 0))
        ![0, -1, 0] t ∧
      ∂ₜ (fun s j => (planarMotion quarterMassBody (fun s => 3 + s.val) (fun _ => 5)
        (fun _ => 0)).comTrajectory s j) t ≠ 0 := by
  obtain ⟨-, hplant, hrate⟩ := trim_relative_equilibrium quarterMassBody quarterMassBody_mass
    quarterMassBody_centerOfMass quarterMassBody_inertia 3 5 t
  refine ⟨hplant, ?_⟩
  rw [hrate]
  intro h0
  simpa using congrFun h0 0

-- At the corner `(1/100, -1/100, 1/100, -1/100)` of the box the actuators are within their bounds.
example : 1 / 10 < actuatorForce (1 / 100) (-1 / 100) 0 ∧
    actuatorForce (1 / 100) (-1 / 100) 0 < 1 / 5 ∧ |actuatorForce (1 / 100) (-1 / 100) 1| < 1 / 20 ∧
    |pitchMoment (1 / 100) (-1 / 100)| ≤ 3 / 100 := by
  have he : (![1 / 100, -1 / 100, 1 / 100, -1 / 100] : Fin 4 → ℝ) ∈ actuatorBox := by
    intro i
    fin_cases i <;> norm_num [abs_div]
  obtain ⟨-, h1, h2, h3, h4⟩ := actuatorBox_bounds he
  exact ⟨h1, h2, h3, h4⟩

-- A state with no forward speed, `x = -1`, has `V = 0`: it is outside the box, and no motion is a
-- plant solution there.
example (M : RigidBodyMotion 3) (g : Fin 3 → ℝ) (t : Time) :
    flightSpeed (-1) 0 = 0 ∧ ¬ SixDofPlant longitudinalMaps (fun _ => ![-1, 0, 0, 0]) M g t := by
  have hV : flightSpeed (-1) 0 = 0 := by simp [flightSpeed]
  obtain ⟨h1, h2⟩ := longitudinalMaps_rejects (x := fun _ => ![-1, 0, 0, 0]) M g t
  exact ⟨hV, h2 (h1 hV)⟩

/-! ## E. Linearization about the trim -/

/-- **A nonzero fixture.** At `δ = (1/100, -1/100, 1/100, 1/100)`, with nonzero `x` and `θ`, the
cubic term is `-x³ = -1/1000000`, `θ - sin θ` is positive, the sup norm is `1/100`, and the cubic
bound with `r = 1/100` is attained: `|-x³| = r ‖δ‖²`. -/
lemma longitudinalRemainder_fixture :
    longitudinalRemainder ![1 / 100, -1 / 100, 1 / 100, 1 / 100] 0 = -1 / 1000000 ∧
      0 < longitudinalRemainder ![1 / 100, -1 / 100, 1 / 100, 1 / 100] 3 ∧
      ‖(![1 / 100, -1 / 100, 1 / 100, 1 / 100] : Fin 4 → ℝ)‖ = 1 / 100 ∧
      |longitudinalRemainder ![1 / 100, -1 / 100, 1 / 100, 1 / 100] 0| =
        1 / 100 * ‖(![1 / 100, -1 / 100, 1 / 100, 1 / 100] : Fin 4 → ℝ)‖ ^ 2 := by
  have hn : ‖(![1 / 100, -1 / 100, 1 / 100, 1 / 100] : Fin 4 → ℝ)‖ = 1 / 100 := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_) ?_
    · fin_cases i <;> norm_num [abs_of_pos]
    · calc (1 : ℝ) / 100 = ‖(![1 / 100, -1 / 100, 1 / 100, 1 / 100] : Fin 4 → ℝ) 0‖ := by
            norm_num
        _ ≤ _ := norm_le_pi_norm _ 0
  refine ⟨by norm_num [longitudinalRemainder], ?_, hn, ?_⟩
  · simp only [longitudinalRemainder, Matrix.cons_val]
    exact sub_pos.2 (Real.sin_lt (by norm_num))
  · rw [hn]
    norm_num [longitudinalRemainder]

/-- Every coordinate of the fixture `(1/100, -1/100, 1/100, 1/100)` is at most `1/100` in absolute
value. -/
private lemma fixture_mem_box :
    ∀ i, |(![1 / 100, -1 / 100, 1 / 100, 1 / 100] : Fin 4 → ℝ) i| ≤ 1 / 100 := by
  intro i
  fin_cases i <;> norm_num [abs_div]

-- The pitch-restoring entry of the Jacobian, read off its block form: `∂q'/∂θ = -1`.
example : longitudinalJacobian 3 2 = -1 := by
  rw [longitudinalJacobian_eq_fromBlocks]
  rfl

-- A pitch perturbation alone produces, to first order, the pitch acceleration `-θ`: the derivative
-- at the trim in the direction `(0, 0, 1, 0)` is `(0, 0, 0, -1)`.
example : fderiv ℝ reducedField 0 ![0, 0, 1, 0] = ![0, 0, 0, -1] := by
  rw [hasFDerivAt_reducedField_zero.fderiv]
  ext i
  fin_cases i <;> simp [Matrix.toLin'_apply, longitudinalJacobian]

-- At the fast state `x = 1/100` the field is its linear part plus the cubic term
-- `(-1/1000000, 0, 0, 0)`.
example : reducedField ![1 / 100, 0, 0, 0] =
    longitudinalJacobian *ᵥ ![1 / 100, 0, 0, 0] + ![-(1 / 1000000), 0, 0, 0] := by
  rw [reducedField_eq_mulVec_add_remainder]
  congr 1
  ext i
  fin_cases i <;> norm_num [longitudinalRemainder]

-- The first-order remainder of the uncertainty-propagation API at the fixture is the cubic term.
example : Statistics.UncertaintyPropagation.jacobianRemainder reducedField 0
    ![1 / 100, -1 / 100, 1 / 100, 1 / 100] 0 = -1 / 1000000 := by
  rw [jacobianRemainder_reducedField]
  exact longitudinalRemainder_fixture.1

-- With `r = 1/100` the fixture is admitted and its pitch remainder is within `(r / 6) ‖δ‖²`.
example : (![1 / 100, -1 / 100, 1 / 100, 1 / 100] : Fin 4 → ℝ) ∈ actuatorBox ∧
    |longitudinalRemainder ![1 / 100, -1 / 100, 1 / 100, 1 / 100] 3| ≤
      1 / 100 / 6 * ‖(![1 / 100, -1 / 100, 1 / 100, 1 / 100] : Fin 4 → ℝ)‖ ^ 2 := by
  obtain ⟨hA, -, -, -, h3⟩ := longitudinalRemainder_bounds (by norm_num) le_rfl fixture_mem_box
  exact ⟨hA, h3⟩

-- The reduced field is differentiable everywhere.
example : Differentiable ℝ reducedField :=
  contDiff_reducedField.differentiable (by norm_num)

-- The second derivative of the forward component at `x = 1/100` along `(1, 0, 0, 0)` is `-6/100`;
-- that of the pitch component at the trim along `(0, 0, 1, 0)` is `0`.
example : fderiv ℝ (fderiv ℝ fun e => reducedField e 0) ![1 / 100, 0, 0, 0] ![1, 0, 0, 0]
      ![1, 0, 0, 0] = -6 / 100 ∧
    fderiv ℝ (fderiv ℝ fun e => reducedField e 3) 0 ![0, 0, 1, 0] ![0, 0, 1, 0] = 0 := by
  obtain ⟨h0, -, -, -⟩ :=
    fderiv_fderiv_reducedField_apply ![1 / 100, 0, 0, 0] ![1, 0, 0, 0] ![1, 0, 0, 0]
  obtain ⟨-, -, -, h3⟩ := fderiv_fderiv_reducedField_apply 0 ![0, 0, 1, 0] ![0, 0, 1, 0]
  rw [h0, h3]
  norm_num

-- At the trim, the box of radius `0`, the Hessian of the forward component vanishes.
example : ‖fderiv ℝ (fderiv ℝ fun e => reducedField e 0) (0 : Fin 4 → ℝ)‖ = 0 := by
  have h := norm_fderiv_fderiv_reducedField_le (r := 0) (y := 0) (fun j => by simp) 0
  simp only [Matrix.cons_val_zero, mul_zero] at h
  exact le_antisymm h (by positivity)

-- The componentwise Hessian theorem at the fixture, `r = 1/100`: the forward remainder is at most
-- `3 r ‖δ‖² = 3/1000000`.
example : |Statistics.UncertaintyPropagation.jacobianRemainder reducedField 0
    ![1 / 100, -1 / 100, 1 / 100, 1 / 100] 0| ≤ 3 / 1000000 := by
  have h := jacobianRemainder_reducedField_le_of_hessian (by norm_num : (0 : ℝ) < 1 / 100)
    fixture_mem_box 0
  rw [longitudinalRemainder_fixture.2.2.1] at h
  calc _ ≤ _ := h
    _ = 3 / 1000000 := by norm_num

-- The all-ones state has sup norm `1`, so its Euclidean norm is at most `2`.
example : ‖(WithLp.toLp 2 fun _ : Fin 4 => (1 : ℝ) : EuclideanSpace ℝ (Fin 4))‖ ≤ 2 := by
  have h := (norm_ofLp_le_norm_le_two_mul (WithLp.toLp 2 fun _ : Fin 4 => (1 : ℝ))).2
  have h1 : ‖(WithLp.ofLp (WithLp.toLp 2 fun _ : Fin 4 => (1 : ℝ)) : Fin 4 → ℝ)‖ = 1 := by
    simp
  rw [h1, mul_one] at h
  exact h

-- A state of Euclidean norm at most `1/100` is admitted, coordinate by coordinate.
example (e : EuclideanSpace ℝ (Fin 4)) (he : ‖e‖ ≤ 1 / 100) : WithLp.ofLp e ∈ actuatorBox :=
  fun i => abs_ofLp_le_of_norm_le he i

-- On the Euclidean ball of radius `1/100` the pitch remainder is at most `‖e‖² / 600`.
example (e : EuclideanSpace ℝ (Fin 4)) (he : ‖e‖ ≤ 1 / 100) :
    |WithLp.ofLp e 2 - Real.sin (WithLp.ofLp e 2)| ≤ ‖e‖ ^ 2 / 600 := by
  have h := (longitudinalRemainder_bounds_euclidean (by norm_num) le_rfl he).2.2.2.2
  simp only [longitudinalRemainder, Matrix.cons_val] at h
  linarith

-- The trim of the quarter-mass body from `(3, 5)` moves forward with rate at least `99/100`.
example (t : Time) : 99 / 100 ≤ ∂ₜ (fun s : Time => 3 + s.val) t :=
  planar_sixDofPlant_forward_rate (trim_relative_equilibrium quarterMassBody quarterMassBody_mass
    quarterMassBody_centerOfMass quarterMassBody_inertia 3 5 t).2.1

end PhyslibExtTest.Mechanics.FlightPlant
