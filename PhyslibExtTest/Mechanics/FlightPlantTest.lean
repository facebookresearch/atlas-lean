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
public import MathlibExt.LinearAlgebra.Matrix.SylvesterCriterion

/-!
# Tests for `PhyslibExt.Mechanics.FlightPlant`

Consumers of the translational correspondence, of the six-degree-of-freedom package and of the
coefficient-map wrapper: straight flight, the admitted domain of a lift map, a unit point mass,
a steady level turn, the controlled longitudinal fixture, its linearization about the trim, the
Lyapunov certificate of that linearization and the local decay of the nonlinear reduced flight.

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

The Lyapunov certificate: the pitch-block entry `1/2` of `P`, read off its block form; the
derivative of the reduced field at the trim in the pitch-rate direction, `(0, 0, 1, -2)`; the
positive determinant of `P` and the entry `-1` of `Aᵀ P + P A`; the bounds `1 ≤ V ≤ 8` at the
all-ones state; `V` and its orbital derivative vanish at the trim, while at `(0, 0, 1, 0)` the
derivative of `V` in the pitch-rate direction is `1` and the orbital derivative is `-1`. From the
trim the actual solution is the zero solution; from `(1, 0, 1, 0)` it is
`(e^{-t}, 0, (1 + t) e^{-t}, -t e^{-t})`, which obeys the decay bound. The determinants of the
certificate and `Aᵀ P` are checked entry by entry, and the solution `exp` of `y' = y` violates the
decay bound.

The nonlinear reduced flight: the field at the pitch-rate state `(0, 0, 0, 1)` is `(0, 0, 1, -2)`,
and at `x = 1` its forward component is the linear part plus the cubic remainder; the orbital
derivative is `-2` at `(1, 0, 0, 0)` and at most `-1/20000` at `(0, 0, 1/100, 0)`, negative there
and not negative at the trim. The state `(1/400, 0, 0, 0)` lies in the invariant sublevel set and
the actuator box; from it a forward solution exists, and it has decayed to at most `√8 e⁻⁵ / 400`
at `t = 40`. Every forward solution from the trim stays there, by sublevel invariance at level `0`
and by the decay bound. From `(1, 1, 1, 1) / 1000`, strictly inside the sublevel set, the solution
stays in the ball `‖e‖ ≤ 1/100` and obeys the conditional decay at `t = 8`. The inverted trim
`(0, 0, π, 0)` is an equilibrium outside the ball whose constant solution does not decay, and from
a state on the sphere `‖e‖ = 1/100`, where the Lyapunov inequality holds, no forward solution stays
in the ball.

## ii. Key results

- `straightFlight`, `liftMaps`, `straightFlight_fixture`, `straightFlight_balanceLaws`,
  `liftMaps_not_sixDofPlant` : the straight-flight fixture.
- `trim_fixture` : the trim of the controlled longitudinal fixture.
- `longitudinalRemainder_fixture` : the nonlinear remainder at a nonzero state.
- `longitudinalLyapunov_fixture`, `linearReducedField_solution_fixture`,
  `exp_violates_decay_bound` : the certificate's entries, a nonzero solution of the linear plant
  and an unstable contrast.
- `nonlinearReducedField_trim`, `nonlinearReducedField_fixture`,
  `nonlinearReducedField_inverted_trim`, `nonlinearReducedField_exits_closedBall` : the trim, a
  nonzero state inside the invariant sublevel set, the inverted trim and the sphere exit of the
  nonlinear reduced flight.

## iii. Table of contents

- A. Straight flight
- B. Consumers of the public lemmas
- C. A steady level turn
- D. The controlled longitudinal fixture
- E. Linearization about the trim
- F. The Lyapunov certificate for the reduced linear plant
- G. Local existence and decay of the nonlinear reduced flight

## iv. References

- `PhyslibExt.Mechanics.FlightPlant`, `PhyslibExt.Mechanics.RigidMotionPorts`,
  `PhyslibExt.Statistics.UncertaintyPropagation` and
  `MathlibExt.LinearAlgebra.Matrix.SylvesterCriterion`.
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


/-! ## F. The Lyapunov certificate for the reduced linear plant -/

/-- **Fixture: the certificate entries.** The pitch block `[[3/2, 1/2], [1/2, 1/2]]` has
determinant `1/2`; the leading principal minors of `P` are `1/2`, `1/4`, `3/8` and `1/8`; and
`Aᵀ P` is `-(1/2) • 1` plus a skew part with entries `∓1/2` at `(θ, q)` and `(q, θ)`, which
cancels in `Aᵀ P + P A = Aᵀ P + (Aᵀ P)ᵀ`. -/
lemma longitudinalLyapunov_fixture :
    !![(3 / 2 : ℝ), 1 / 2; 1 / 2, 1 / 2].det = 1 / 2 ∧
      (longitudinalLyapunovMatrix.leadingPrincipalSubmatrix 1 (by norm_num)).det = 1 / 2 ∧
      (longitudinalLyapunovMatrix.leadingPrincipalSubmatrix 2 (by norm_num)).det = 1 / 4 ∧
      (longitudinalLyapunovMatrix.leadingPrincipalSubmatrix 3 (by norm_num)).det = 3 / 8 ∧
      longitudinalLyapunovMatrix.det = 1 / 8 ∧
      longitudinalJacobianᵀ * longitudinalLyapunovMatrix =
        !![-1 / 2, 0, 0, 0; 0, -1 / 2, 0, 0; 0, 0, -1 / 2, -1 / 2; 0, 0, 1 / 2, -1 / 2] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    norm_num
  · simp [Matrix.leadingPrincipalSubmatrix, longitudinalLyapunovMatrix]
  · rw [Matrix.det_fin_two]
    simp [Matrix.leadingPrincipalSubmatrix, longitudinalLyapunovMatrix]
    norm_num
  · rw [Matrix.det_fin_three]
    simp [Matrix.leadingPrincipalSubmatrix, longitudinalLyapunovMatrix]
    norm_num
  · rw [longitudinalLyapunovMatrix_eq_fromBlocks, Matrix.det_reindex_self,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_fin_two]
    simp
    norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [longitudinalJacobian, longitudinalLyapunovMatrix, Matrix.mul_apply,
        Fin.sum_univ_four] <;>
      norm_num

/-- **Fixture: a nonzero solution.** From `e₀ = (1, 0, 1, 0)` the actual solution of the reduced
linear plant is `(e^{-t}, 0, (1 + t) e^{-t}, -t e^{-t})`: the pitch block `[[0, 1], [-1, -2]]`
has the double eigenvalue `-1` (critical damping), hence the `t e^{-t}` terms. -/
lemma linearReducedField_solution_fixture (e : ℝ → EuclideanSpace ℝ (Fin 4))
    (he : ∀ s, e s = WithLp.toLp 2
      ![Real.exp (-s), 0, (1 + s) * Real.exp (-s), -s * Real.exp (-s)]) :
    e 0 = WithLp.toLp 2 ![1, 0, 1, 0] ∧ ∀ t, HasDerivAt e (linearReducedField (e t)) t := by
  refine ⟨by simp [he], fun t => ?_⟩
  let g : ℝ → Fin 4 → ℝ := fun s =>
    ![Real.exp (-s), 0, (1 + s) * Real.exp (-s), -s * Real.exp (-s)]
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  have hAg : longitudinalJacobian *ᵥ g t =
      ![-Real.exp (-t), 0, -t * Real.exp (-t), t * Real.exp (-t) - Real.exp (-t)] := by
    ext i
    fin_cases i
    all_goals simp [g, longitudinalJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  have hg : HasDerivAt g (longitudinalJacobian *ᵥ g t) t := by
    rw [hAg, hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa [g] using hexp
    · simpa [g] using hasDerivAt_const t (0 : ℝ)
    · change HasDerivAt (fun x => (1 + x) * Real.exp (-x)) (-t * Real.exp (-t)) t
      exact (((hasDerivAt_id' t).const_add 1).fun_mul hexp).congr_deriv (by ring)
    · change HasDerivAt (fun x => -x * Real.exp (-x)) (t * Real.exp (-t) - Real.exp (-t)) t
      exact ((hasDerivAt_id' t).fun_neg.fun_mul hexp).congr_deriv (by ring)
  have hfun : e = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm ∘ g := by
    funext s
    rw [he s]
    rfl
  rw [hfun]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt
    t hg

/-- **Contrast: an unstable scalar plant.** The actual solution `exp` of `y' = y`, `y 0 = 1`,
violates the decay bound of the reduced linear plant (at `t = 4`, `e⁴ > √8 e⁻¹`): the bound comes
from the certificate, not from linearity. -/
lemma exp_violates_decay_bound :
    (∀ t, HasDerivAt Real.exp (Real.exp t) t) ∧ Real.exp 0 = 1 ∧
      ¬ ∀ t, 0 ≤ t → |Real.exp t| ≤ Real.sqrt 8 * Real.exp (-t / 4) * |Real.exp 0| := by
  refine ⟨Real.hasDerivAt_exp, Real.exp_zero, fun h => ?_⟩
  have h4 := h 4 (by norm_num)
  rw [Real.exp_zero, abs_one, mul_one, abs_of_pos (Real.exp_pos 4)] at h4
  have hs : Real.sqrt 8 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h5 : (6 : ℝ) ≤ Real.exp 5 := by linarith [Real.add_one_le_exp 5]
  have hsplit : Real.exp 5 = Real.exp 4 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have hinv : Real.exp (-4 / 4) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have h1 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith [mul_le_mul_of_nonneg_right h4 h1.le]

-- The pitch-block entry of the Lyapunov matrix, read off its block form: `P θq = 1/2`.
example : longitudinalLyapunovMatrix 2 3 = 1 / 2 := by
  rw [longitudinalLyapunovMatrix_eq_fromBlocks]
  rfl

-- A pitch-rate perturbation alone produces, to first order, the pitch rate `q` and the pitch
-- acceleration `-2 q`: the linear plant, the derivative of the reduced field at the trim, maps
-- `(0, 0, 0, 1)` to `(0, 0, 1, -2)`.
example : fderiv ℝ reducedField 0 ![0, 0, 0, 1] = ![0, 0, 1, -2] := by
  have h := linearReducedField_eq_fderiv (WithLp.toLp 2 ![0, 0, 0, 1])
  simp only at h
  rw [← h]
  ext i
  fin_cases i <;> simp [linearReducedField, longitudinalJacobian]

-- The Lyapunov matrix has positive determinant, as every positive definite matrix does, and `1`
-- is symmetric.
example : 0 < longitudinalLyapunovMatrix.det ∧ (1 : Matrix (Fin 4) (Fin 4) ℝ).IsHermitian :=
  ⟨longitudinalLyapunovMatrix_posDef.1.det_pos, longitudinalLyapunovMatrix_posDef.2.isHermitian⟩

-- The pitch-rate entry of `Aᵀ P + P A` is `-1`.
example : (longitudinalJacobianᵀ * longitudinalLyapunovMatrix +
    longitudinalLyapunovMatrix * longitudinalJacobian) 3 3 = -1 := by
  rw [longitudinalLyapunov_equation]
  simp

-- At the all-ones state, of squared Euclidean norm `4`, the comparison bounds give `1 ≤ V ≤ 8`.
example : 1 ≤ longitudinalLyapunov (WithLp.toLp 2 fun _ => 1) ∧
    longitudinalLyapunov (WithLp.toLp 2 fun _ => 1) ≤ 8 := by
  have hn : ‖(WithLp.toLp 2 fun _ : Fin 4 => (1 : ℝ) : EuclideanSpace ℝ (Fin 4))‖ ^ 2 = 4 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
    norm_num
  have h := longitudinalLyapunov_bounds (WithLp.toLp 2 fun _ => 1)
  rw [hn] at h
  constructor <;> linarith [h.1, h.2]

-- `V` vanishes at the trim and nowhere else, for example not at `(1, 0, 0, 0)`.
example : longitudinalLyapunov 0 = 0 ∧
    longitudinalLyapunov (WithLp.toLp 2 ![1, 0, 0, 0]) ≠ 0 := by
  refine ⟨(longitudinalLyapunov_eq_zero_iff 0).2 rfl, fun h => ?_⟩
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 4) => v 0)
    ((longitudinalLyapunov_eq_zero_iff _).1 h)
  simp at h0

-- `V` is differentiable at the trim.
example : DifferentiableAt ℝ longitudinalLyapunov 0 :=
  differentiable_longitudinalLyapunov 0

-- At `(0, 0, 1, 0)` the derivative of `V` in the pitch-rate direction is `2 · (1/2) = 1`.
example : fderiv ℝ longitudinalLyapunov (WithLp.toLp 2 ![0, 0, 1, 0])
    (WithLp.toLp 2 ![0, 0, 0, 1]) = 1 := by
  rw [fderiv_longitudinalLyapunov_apply]
  norm_num [longitudinalLyapunovMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_four]

-- The orbital derivative vanishes at the trim, where nothing decays, and is `-1` at
-- `(0, 0, 1, 0)`.
example : fderiv ℝ longitudinalLyapunov 0 (linearReducedField 0) = 0 ∧
    fderiv ℝ longitudinalLyapunov (WithLp.toLp 2 ![0, 0, 1, 0])
      (linearReducedField (WithLp.toLp 2 ![0, 0, 1, 0])) = -1 := by
  refine ⟨by rw [fderiv_longitudinalLyapunov_linearReducedField]; simp, ?_⟩
  rw [fderiv_longitudinalLyapunov_linearReducedField, EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  norm_num

-- From the trim the actual solution is the zero solution.
example (e : ℝ → EuclideanSpace ℝ (Fin 4)) (h0 : e 0 = 0)
    (hd : ∀ t, HasDerivAt e (linearReducedField (e t)) t) : e = fun _ => 0 :=
  (existsUnique_linearReducedField_solution 0).unique ⟨h0, hd⟩
    ⟨rfl, fun t => by
      simpa [linearReducedField] using hasDerivAt_const t (0 : EuclideanSpace ℝ (Fin 4))⟩

-- From `(1, 0, 1, 0)` the actual solution is the fixture solution.
example (e : ℝ → EuclideanSpace ℝ (Fin 4)) (h0 : e 0 = WithLp.toLp 2 ![1, 0, 1, 0])
    (hd : ∀ t, HasDerivAt e (linearReducedField (e t)) t) (t : ℝ) :
    e t = WithLp.toLp 2 ![Real.exp (-t), 0, (1 + t) * Real.exp (-t), -t * Real.exp (-t)] :=
  congrFun ((existsUnique_linearReducedField_solution _).unique ⟨h0, hd⟩
    (linearReducedField_solution_fixture _ fun _ => rfl)) t

-- The nonzero fixture solution obeys the decay bound at `t = 1`, where its state is
-- `(e⁻¹, 0, 2 e⁻¹, -e⁻¹)`.
example : ‖(WithLp.toLp 2 ![Real.exp (-1), 0, (1 + 1) * Real.exp (-1), -1 * Real.exp (-1)] :
      EuclideanSpace ℝ (Fin 4))‖ ≤
    Real.sqrt 8 * Real.exp (-1 / 4) *
      ‖(WithLp.toLp 2 ![1, 0, 1, 0] : EuclideanSpace ℝ (Fin 4))‖ := by
  obtain ⟨h0, hd⟩ := linearReducedField_solution_fixture
    (fun s => WithLp.toLp 2 ![Real.exp (-s), 0, (1 + s) * Real.exp (-s), -s * Real.exp (-s)])
    fun _ => rfl
  have h := norm_le_of_isIntegralCurveOn_linearReducedField
    (fun s _ => (hd s).hasDerivWithinAt) zero_le_one
  rw [h0] at h
  exact h

-- From the trim, the decay bound keeps the actual solution at `0`.
example (t : ℝ) (ht : 0 ≤ t) : ∃ e : ℝ → EuclideanSpace ℝ (Fin 4), e 0 = 0 ∧ e t = 0 := by
  obtain ⟨e, h0, -, hb⟩ := linearReducedField_solution_decay 0
  refine ⟨e, h0, norm_le_zero_iff.1 ?_⟩
  simpa using hb t ht

/-! ## G. Local existence and decay of the nonlinear reduced flight -/

/-- The squared Euclidean norm in coordinates. -/
private lemma norm_sq_eq_coords (e : EuclideanSpace ℝ (Fin 4)) :
    ‖e‖ ^ 2 = e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2 + e 3 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  simp [Real.norm_eq_abs, sq_abs]

/-- **Fixture: the trim.** The trim is an equilibrium of the nonlinear reduced field, the orbital
derivative vanishes there, and the constant trim state is a forward solution in the actuator box:
the existence statement's solution from `e₀ = 0`, with equality `0 ≤ 0` in the decay bound. -/
lemma nonlinearReducedField_trim :
    nonlinearReducedField 0 = 0 ∧
      fderiv ℝ longitudinalLyapunov 0 (nonlinearReducedField 0) = 0 ∧
      IsIntegralCurveOn (fun _ => (0 : EuclideanSpace ℝ (Fin 4)))
        (fun _ x => nonlinearReducedField x) (Set.Ici 0) ∧
      WithLp.ofLp (0 : EuclideanSpace ℝ (Fin 4)) ∈ actuatorBox := by
  have h0 : nonlinearReducedField 0 = 0 := by
    ext i
    fin_cases i <;> simp [nonlinearReducedField, reducedField]
  refine ⟨h0, by rw [h0, map_zero], fun t _ => ?_, fun i => by simp⟩
  change HasDerivWithinAt _ (nonlinearReducedField 0) _ _
  rw [h0]
  exact hasDerivWithinAt_const _ _ _

/-- **Fixture: a nonzero state strictly inside the invariant sublevel set.** The state
`e₀ = (1, 1, 1, 1) / 1000` has `‖e₀‖ = 1/500 < 1/400` and `V(e₀) = 1/250000 < 1/80000`; the
existence theorem gives a forward solution from it in the actuator box with
`‖e t‖ ≤ √8 * exp (-t / 8) / 500`. -/
lemma nonlinearReducedField_fixture (e₀ : EuclideanSpace ℝ (Fin 4))
    (he₀ : e₀ = WithLp.toLp 2 ![1 / 1000, 1 / 1000, 1 / 1000, 1 / 1000]) :
    e₀ ≠ 0 ∧ ‖e₀‖ = 1 / 500 ∧ longitudinalLyapunov e₀ = 1 / 250000 ∧
      longitudinalLyapunov e₀ < 1 / 80000 ∧
      ∃ e : ℝ → EuclideanSpace ℝ (Fin 4), e 0 = e₀ ∧
        IsIntegralCurveOn e (fun _ x => nonlinearReducedField x) (Set.Ici 0) ∧
        ∀ t, 0 ≤ t → WithLp.ofLp (e t) ∈ actuatorBox ∧
          ‖e t‖ ≤ Real.sqrt 8 * Real.exp (-t / 8) / 500 := by
  have hn2 : ‖e₀‖ ^ 2 = 1 / 250000 := by
    rw [norm_sq_eq_coords, he₀]
    norm_num
  have hn : ‖e₀‖ = 1 / 500 := by
    rw [← Real.sqrt_sq (norm_nonneg e₀), hn2, show (1 : ℝ) / 250000 = (1 / 500) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hV : longitudinalLyapunov e₀ = 1 / 250000 := by
    rw [he₀]
    simp [longitudinalLyapunov, longitudinalLyapunovMatrix, dotProduct, Matrix.mulVec,
      Fin.sum_univ_four]
    norm_num
  obtain ⟨e, h0, he, hb⟩ := nonlinearReducedField_solution_decay e₀ (by rw [hn]; norm_num)
  refine ⟨fun h => by rw [h, norm_zero] at hn; norm_num at hn, hn, hV, by rw [hV]; norm_num,
    e, h0, he, fun t ht => ⟨(hb t ht).1, ?_⟩⟩
  have h := (hb t ht).2
  rw [hn] at h
  linarith

/-- **Invalid example: the inverted trim.** The state `(0, 0, π, 0)` (pitch angle `π`, far outside
the actuator box) is another equilibrium of the nonlinear reduced field, where the orbital
derivative is `0`, not `≤ -(1/2) ‖e‖²`; its constant solution keeps `‖e t‖ = π` and violates the
decay bound (at `t = 16`). The decay is local. -/
lemma nonlinearReducedField_inverted_trim (e₁ : EuclideanSpace ℝ (Fin 4))
    (he₁ : e₁ = WithLp.toLp 2 ![0, 0, Real.pi, 0]) :
    nonlinearReducedField e₁ = 0 ∧ ‖e₁‖ = Real.pi ∧
      fderiv ℝ longitudinalLyapunov e₁ (nonlinearReducedField e₁) = 0 ∧
      IsIntegralCurveOn (fun _ => e₁) (fun _ x => nonlinearReducedField x) (Set.Ici 0) ∧
      ¬ ∀ t, 0 ≤ t → ‖e₁‖ ≤ Real.sqrt 8 * Real.exp (-t / 8) * ‖e₁‖ := by
  have h0 : nonlinearReducedField e₁ = 0 := by
    rw [he₁]
    ext i
    fin_cases i <;> simp [nonlinearReducedField, reducedField]
  have hn : ‖e₁‖ = Real.pi := by
    rw [← Real.sqrt_sq (norm_nonneg e₁), norm_sq_eq_coords, he₁]
    simp [Real.sqrt_sq Real.pi_pos.le]
  refine ⟨h0, hn, by rw [h0, map_zero], fun t _ => ?_, fun h => ?_⟩
  · change HasDerivWithinAt _ (nonlinearReducedField e₁) _ _
    rw [h0]
    exact hasDerivWithinAt_const _ _ _
  · have h16 := h 16 (by norm_num)
    rw [hn] at h16
    have hs8 : Real.sqrt 8 < 3 := by
      rw [show (3 : ℝ) = Real.sqrt 9 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have he2 : 3 ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    have key : Real.sqrt 8 * Real.exp (-16 / 8) < 1 := by
      calc Real.sqrt 8 * Real.exp (-16 / 8) < 3 * Real.exp (-16 / 8) := by
            gcongr
        _ ≤ Real.exp 2 * Real.exp (-16 / 8) := by gcongr
        _ = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [mul_lt_mul_of_pos_right key Real.pi_pos]

/-- **Boundary example: the ball is not invariant.** At `e₂ = (0, 0, θ₂, 10⁻⁸)` with
`θ₂ = √(10⁻⁴ - 10⁻¹⁶)`, on the sphere `‖e₂‖ = 1/100` where the Lyapunov inequality holds, but
outside the invariant sublevel set, `d‖e‖²/dt = 2 q (θ - sin θ - 2 q) > 0`: no forward solution
from `e₂` stays in the ball `‖e‖ ≤ 1/100`, so the conditional decay statement says nothing about
`e₂`. Without the sublevel invariance and continuation steps, the Lyapunov inequality gives only
conditional decay. -/
lemma nonlinearReducedField_exits_closedBall (e₂ : EuclideanSpace ℝ (Fin 4))
    (he₂ : e₂ = WithLp.toLp 2 ![0, 0, Real.sqrt (1 / 10000 - 1 / 10 ^ 16), 1 / 10 ^ 8]) :
    ‖e₂‖ = 1 / 100 ∧ 1 / 80000 < longitudinalLyapunov e₂ ∧
      ∀ e : ℝ → EuclideanSpace ℝ (Fin 4),
        IsIntegralCurveOn e (fun _ x => nonlinearReducedField x) (Set.Ici 0) → e 0 = e₂ →
          ¬ ∀ t, 0 ≤ t → ‖e t‖ ≤ 1 / 100 := by
  set θ := Real.sqrt (1 / 10000 - 1 / 10 ^ 16) with hθdef
  have hθ2 : θ ^ 2 = 1 / 10000 - 1 / 10 ^ 16 := Real.sq_sqrt (by norm_num)
  have hθ0 : 0 ≤ θ := Real.sqrt_nonneg _
  have hθlo : 99 / 10000 ≤ θ := by nlinarith
  have hθhi : θ ≤ 1 / 100 := by nlinarith
  have hn2 : ‖e₂‖ ^ 2 = 1 / 10000 := by
    rw [norm_sq_eq_coords, he₂]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [hθ2]
    norm_num
  have hn : ‖e₂‖ = 1 / 100 := by
    rw [← Real.sqrt_sq (norm_nonneg e₂), hn2, show (1 : ℝ) / 10000 = (1 / 100) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hsin : 2 / 10 ^ 8 < θ - Real.sin θ := by
    have hb := Real.sin_bound (x := θ) (by rw [abs_of_nonneg hθ0]; linarith)
    rw [abs_of_nonneg hθ0] at hb
    have h1 := (abs_le.1 hb).2
    have h3 : (99 / 10000 : ℝ) ^ 3 ≤ θ ^ 3 := pow_le_pow_left₀ (by norm_num) hθlo 3
    have h5 : θ ^ 5 ≤ (1 / 100 : ℝ) ^ 5 := pow_le_pow_left₀ hθ0 hθhi 5
    nlinarith
  refine ⟨hn, ?_, fun e he h0 hball => ?_⟩
  · rw [he₂]
    simp [longitudinalLyapunov, longitudinalLyapunovMatrix, dotProduct, Matrix.mulVec,
      Fin.sum_univ_four]
    nlinarith
  · have hmax : IsLocalMaxOn (fun t => ‖e t‖ ^ 2) (Set.Ici 0) 0 := by
      refine IsMaxOn.isLocalMaxOn fun t ht => ?_
      have h1 := hball t ht
      have h2 : ‖e t‖ ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      change ‖e t‖ ^ 2 ≤ ‖e 0‖ ^ 2
      rw [h0, hn2]
      linarith
    have hd := (he 0 (Set.mem_Ici.2 le_rfl)).norm_sq
    have hseg : segment ℝ (0 : ℝ) (0 + 1) ⊆ Set.Ici 0 := by
      rw [zero_add, segment_eq_Icc zero_le_one]
      exact Set.Icc_subset_Ici_self
    have hneg := hmax.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt
      (mem_posTangentConeAt_of_segment_subset hseg)
    rw [h0, PiLp.inner_apply, Fin.sum_univ_four] at hneg
    simp [he₂, nonlinearReducedField, reducedField] at hneg
    nlinarith


-- The field at the pitch-rate state `(0, 0, 0, 1)` is `(0, 0, 1, -2)`.
example : nonlinearReducedField (WithLp.toLp 2 ![0, 0, 0, 1]) = WithLp.toLp 2 ![0, 0, 1, -2] := by
  ext i
  fin_cases i <;> simp [nonlinearReducedField, reducedField]

-- At `x = 1` the forward component `-2` is the linear part `-1` plus the cubic remainder `-1`.
example : WithLp.ofLp (nonlinearReducedField (WithLp.toLp 2 ![1, 0, 0, 0])) 0 = -1 + -1 := by
  rw [ofLp_nonlinearReducedField]
  simp [linearReducedField, longitudinalJacobian, longitudinalRemainder]

-- The orbital derivative identity holds at every state: at `(1, 0, 0, 0)`, far outside the ball,
-- `V' = -‖e‖² - x⁴ = -2`.
example : fderiv ℝ longitudinalLyapunov (WithLp.toLp 2 ![1, 0, 0, 0])
    (nonlinearReducedField (WithLp.toLp 2 ![1, 0, 0, 0])) = -2 := by
  rw [fderiv_longitudinalLyapunov_nonlinearReducedField, norm_sq_eq_coords]
  norm_num

-- At `(0, 0, 1/100, 0)`, on the sphere `‖e‖ = 1/100`, the Lyapunov inequality gives
-- `V' ≤ -1/20000`.
example : fderiv ℝ longitudinalLyapunov (WithLp.toLp 2 ![0, 0, 1 / 100, 0])
    (nonlinearReducedField (WithLp.toLp 2 ![0, 0, 1 / 100, 0])) ≤ -1 / 20000 := by
  have hn2 : ‖(WithLp.toLp 2 ![0, 0, 1 / 100, 0] : EuclideanSpace ℝ (Fin 4))‖ ^ 2 =
      1 / 10000 := by
    rw [norm_sq_eq_coords]
    norm_num
  have hn : ‖(WithLp.toLp 2 ![0, 0, 1 / 100, 0] : EuclideanSpace ℝ (Fin 4))‖ ≤ 1 / 100 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 ![0, 0, 1 / 100, 0] : EuclideanSpace ℝ (Fin 4))]
  have h := (fderiv_longitudinalLyapunov_nonlinearReducedField_le hn).1
  rw [hn2] at h
  linarith

-- The orbital derivative is negative at the nonzero state `(0, 0, 1/100, 0)` of the ball and not
-- negative at the trim.
example : fderiv ℝ longitudinalLyapunov (WithLp.toLp 2 ![0, 0, 1 / 100, 0])
      (nonlinearReducedField (WithLp.toLp 2 ![0, 0, 1 / 100, 0])) < 0 ∧
    ¬ fderiv ℝ longitudinalLyapunov 0 (nonlinearReducedField 0) < 0 := by
  have hn2 : ‖(WithLp.toLp 2 ![0, 0, 1 / 100, 0] : EuclideanSpace ℝ (Fin 4))‖ ^ 2 =
      1 / 10000 := by
    rw [norm_sq_eq_coords]
    norm_num
  have hn : ‖(WithLp.toLp 2 ![0, 0, 1 / 100, 0] : EuclideanSpace ℝ (Fin 4))‖ ≤ 1 / 100 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 ![0, 0, 1 / 100, 0] : EuclideanSpace ℝ (Fin 4))]
  refine ⟨(fderiv_longitudinalLyapunov_nonlinearReducedField_neg_iff hn).2 fun h => ?_,
    fun h => (fderiv_longitudinalLyapunov_nonlinearReducedField_neg_iff (by simp)).1 h rfl⟩
  rw [h, norm_zero] at hn2
  norm_num at hn2

-- The state `(1/400, 0, 0, 0)` on the start sphere has `V ≤ 1/80000` and lies in the actuator box.
example : longitudinalLyapunov (WithLp.toLp 2 ![1 / 400, 0, 0, 0]) ≤ 1 / 80000 ∧
    WithLp.ofLp (WithLp.toLp 2 ![(1 / 400 : ℝ), 0, 0, 0]) ∈ actuatorBox := by
  have hn2 : ‖(WithLp.toLp 2 ![1 / 400, 0, 0, 0] : EuclideanSpace ℝ (Fin 4))‖ ^ 2 =
      1 / 160000 := by
    rw [norm_sq_eq_coords]
    norm_num
  have hV := longitudinalLyapunov_sublevel_spec.2.1 (WithLp.toLp 2 ![1 / 400, 0, 0, 0])
    (by nlinarith [norm_nonneg (WithLp.toLp 2 ![1 / 400, 0, 0, 0] : EuclideanSpace ℝ (Fin 4))])
  exact ⟨hV, (longitudinalLyapunov_sublevel_spec.2.2 _ hV).2⟩

-- Sublevel invariance at level `0`: every forward solution from the trim stays at the trim.
example (e : ℝ → EuclideanSpace ℝ (Fin 4))
    (he : IsIntegralCurveOn e (fun _ x => nonlinearReducedField x) (Set.Ici 0)) (h0 : e 0 = 0)
    (t : ℝ) (ht : 0 ≤ t) : e t = 0 := by
  have h := mapsTo_sublevel_of_isIntegralCurveOn_nonlinearReducedField he (c := 0)
    (by norm_num) (by rw [h0, (longitudinalLyapunov_eq_zero_iff 0).2 rfl]) (Set.mem_Ici.2 ht)
  exact (longitudinalLyapunov_eq_zero_iff _).1 (le_antisymm h
    (by nlinarith [(longitudinalLyapunov_bounds (e t)).1, sq_nonneg ‖e t‖]))

-- The forward solution from the fixture state stays in the ball `‖e‖ ≤ 1/100`, so the
-- conditional decay applies to it: at `t = 8`, `‖e 8‖ ≤ √8 e⁻¹ / 500`.
example : ∃ e : ℝ → EuclideanSpace ℝ (Fin 4),
    e 0 = WithLp.toLp 2 ![1 / 1000, 1 / 1000, 1 / 1000, 1 / 1000] ∧
      ‖e 8‖ ≤ Real.sqrt 8 * Real.exp (-1) / 500 := by
  obtain ⟨-, hn, -, -, e, h0, he, hb⟩ := nonlinearReducedField_fixture _ rfl
  have hs8 : Real.sqrt 8 < 3 := by
    rw [show (3 : ℝ) = Real.sqrt 9 by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hball : ∀ t, 0 ≤ t → ‖e t‖ ≤ 1 / 100 := fun t ht => by
    have h := (hb t ht).2
    have hexp : Real.exp (-t / 8) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    nlinarith [Real.exp_pos (-t / 8), Real.sqrt_nonneg 8]
  refine ⟨e, h0, ?_⟩
  have h := norm_le_of_isIntegralCurveOn_nonlinearReducedField_of_norm_le he hball
    (t := 8) (by norm_num)
  rw [h0, hn, show (-8 : ℝ) / 8 = -1 by norm_num] at h
  linarith

-- From the trim the decay bound forces every forward solution to stay at `0`.
example (e : ℝ → EuclideanSpace ℝ (Fin 4))
    (he : IsIntegralCurveOn e (fun _ x => nonlinearReducedField x) (Set.Ici 0)) (h0 : e 0 = 0)
    (t : ℝ) (ht : 0 ≤ t) : e t = 0 := by
  have h := norm_le_of_isIntegralCurveOn_nonlinearReducedField he (by rw [h0, norm_zero]; norm_num)
    ht
  rw [h0, norm_zero, mul_zero] at h
  exact norm_le_zero_iff.1 h

-- From `(1/400, 0, 0, 0)`, on the boundary of the start ball, a forward solution exists in the
-- actuator box.
example : ∃ e : ℝ → EuclideanSpace ℝ (Fin 4), e 0 = WithLp.toLp 2 ![1 / 400, 0, 0, 0] ∧
    IsIntegralCurveOn e (fun _ x => nonlinearReducedField x) (Set.Ici 0) ∧
    ∀ t, 0 ≤ t → WithLp.ofLp (e t) ∈ actuatorBox := by
  have hn2 : ‖(WithLp.toLp 2 ![1 / 400, 0, 0, 0] : EuclideanSpace ℝ (Fin 4))‖ ^ 2 =
      1 / 160000 := by
    rw [norm_sq_eq_coords]
    norm_num
  exact exists_nonlinearReducedField_solution _
    (by nlinarith [norm_nonneg (WithLp.toLp 2 ![1 / 400, 0, 0, 0] : EuclideanSpace ℝ (Fin 4))])

-- From `(1/400, 0, 0, 0)` the solution of the headline has decayed to at most `√8 e⁻⁵ / 400` at
-- `t = 40`.
example : ∃ e : ℝ → EuclideanSpace ℝ (Fin 4), e 0 = WithLp.toLp 2 ![1 / 400, 0, 0, 0] ∧
    ‖e 40‖ ≤ Real.sqrt 8 * Real.exp (-5) / 400 := by
  have hn2 : ‖(WithLp.toLp 2 ![1 / 400, 0, 0, 0] : EuclideanSpace ℝ (Fin 4))‖ ^ 2 =
      1 / 160000 := by
    rw [norm_sq_eq_coords]
    norm_num
  have hn : ‖(WithLp.toLp 2 ![1 / 400, 0, 0, 0] : EuclideanSpace ℝ (Fin 4))‖ = 1 / 400 := by
    rw [← Real.sqrt_sq (norm_nonneg _), hn2,
      show (1 : ℝ) / 160000 = (1 / 400) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  obtain ⟨e, h0, -, hb⟩ := nonlinearReducedField_solution_decay _ (le_of_eq hn)
  refine ⟨e, h0, ?_⟩
  have h := (hb 40 (by norm_num)).2
  rw [hn, show (-40 : ℝ) / 8 = -5 by norm_num] at h
  linarith

-- The inverted trim's constant solution never enters the ball `‖e‖ ≤ 1/100`, so the conditional
-- decay says nothing about it, and it does not decay.
example : ¬ ∀ t, 0 ≤ t →
    ‖(WithLp.toLp 2 ![0, 0, Real.pi, 0] : EuclideanSpace ℝ (Fin 4))‖ ≤ 1 / 100 := by
  obtain ⟨-, hn, -⟩ := nonlinearReducedField_inverted_trim _ rfl
  intro h
  have h0 := h 0 le_rfl
  rw [hn] at h0
  linarith [Real.two_le_pi]

-- At the sphere state of the boundary fixture the Lyapunov inequality holds, yet no forward
-- solution from it stays in the ball: the inequality alone gives only conditional decay.
example (e₂ : EuclideanSpace ℝ (Fin 4))
    (he₂ : e₂ = WithLp.toLp 2 ![0, 0, Real.sqrt (1 / 10000 - 1 / 10 ^ 16), 1 / 10 ^ 8]) :
    fderiv ℝ longitudinalLyapunov e₂ (nonlinearReducedField e₂) ≤ -(1 / 2) * ‖e₂‖ ^ 2 ∧
      ∀ e : ℝ → EuclideanSpace ℝ (Fin 4),
        IsIntegralCurveOn e (fun _ x => nonlinearReducedField x) (Set.Ici 0) → e 0 = e₂ →
          ¬ ∀ t, 0 ≤ t → ‖e t‖ ≤ 1 / 100 := by
  obtain ⟨hn, -, hexit⟩ := nonlinearReducedField_exits_closedBall e₂ he₂
  exact ⟨(fderiv_longitudinalLyapunov_nonlinearReducedField_le hn.le).1, hexit⟩

end PhyslibExtTest.Mechanics.FlightPlant
