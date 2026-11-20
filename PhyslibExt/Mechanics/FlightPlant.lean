/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.RigidMotionPorts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Six-degree-of-freedom flight plant: the translational port and a controlled longitudinal trim

The body-axis translational equation of a rigid motion's centre of mass, derived from the
rotating-frame transport law, paired with the existing Euler equations of the same motion, the
plant defined by aerodynamic and propulsive force and moment maps on an admitted domain, and a
synthetic controlled longitudinal fixture of that plant with its trim and actuator domain.

## i. Overview

A rigid vehicle is a Physlib `RigidBodyMotion` `M`: its mass `m = M.mass`, constant since the
mass distribution is body-fixed, the inertial coordinates `X(t)` of its centre-of-mass trajectory
and its orientation `R(t) ∈ SO(3)`, with the body-to-inertial convention `v_I = R v_B` of
`Units.EngineeringFrames`. The body velocity is `v_B = Rᵀ X'`, the velocity of the centre of mass
in body components (for a differentiable trajectory, `X'` has the components of Physlib's
`centerOfMassVelocity`, by `Time.derivVec_space`), and `ω_B` is Physlib's body angular velocity,
the vee of `Rᵀ Ṙ`. The translational and the rotational data thus belong to one rigid body.

The translational balance law `m X'' = R F_B + m g` is a model input: `F_B` is the aerodynamic and
propulsive force in body components and `g` the uniform gravitational acceleration in inertial
components. Since `X' = R v_B`, the transport law `d(R u)/dt = R (u' + ω_B × u)` of
`Mechanics.RigidMotionPorts` gives `X'' = R (v_B' + ω_B × v_B)`, and for a `C²` trajectory and
orientation the law holds exactly when

`v_B' = F_B / m + Rᵀ g - ω_B × v_B`

in body components. The rotational half is not proved again: `Mechanics.RigidMotionPorts`
transports the balance law `dL_COM/dt = τ_I` to Euler's equations
`I_B ω_B' + ω_B × (I_B ω_B) = Rᵀ τ_I`. The six-degree-of-freedom body equations pair the
translational equation with that Euler equation, and both inertial laws hold exactly when the pair
does.

Aerodynamic and propulsive maps are explicit model inputs with admitted domains: a force map and a
moment map defined only on the admitted states (a polar validity region, for example), so they are
never evaluated elsewhere. The plant itself requires positive mass and `C²` data on an open set of
times around the given time: without them the totalized inverse `m⁻¹ = 0` at `m = 0` would drop the
force from the translational equation, and `∂ₜ` of a nondifferentiable curve is a fallback value.
For a body frame centered at the centre of mass, the plant holds exactly when, in addition, the
state is admitted and the inertial laws hold with the force and the moment the maps give.

Section D is a synthetic ideal-force-controlled longitudinal fixture of the plant, in
nondimensional units with mass, pitch inertia, gravity, trim speed, air density and reference
area `1`; it is not a measured aircraft. The forward/up plane is spanned by the first two
inertial axes, gravity is `(0, -1, 0)`, and the pitch angle `θ` is the rotation `Rz(θ)` of
`Units.EngineeringFrames` about the third axis, so `θ > 0` turns the body forward axis
`R e₁ = (cos θ, sin θ, 0)` from forward toward up (nose up); it is not an aviation body-axis sign
convention. The state `(x, z, θ, q)` has the velocity `(1 + x, z, 0)`, the speed
`V = √((1 + x)² + z²)`, the pitch angle `θ` and the pitch rate `q`. The lift `½ V² C_L`, with
`C_L = 2`, acts along the velocity turned a quarter turn toward up, and the drag `½ V² C_D`, with
the polar `C_D = 1/10 + C_L²/20 = 3/10`, against it; both are written without division, so they
are defined (and zero) at `V = 0`, and both are independent of the attitude. The ideal vector
force actuator `A = (-x - x³, 1 - z, 0) - F_aero` and the pitch-moment actuator `M = -2 q - sin θ`
are explicit parts of the model, and the maps are admitted on the box of radius `1/100` in each
state coordinate. For a body of mass `1`, centre of mass `0` and unit pitch inertia about a
principal third axis, a planar motion (centre of mass in the forward/up plane, orientation
`Rz(θ)`) is a plant solution exactly when its state is in the box and obeys `x' = -x - x³`,
`z' = -z`, `θ' = q`, `q' = -2 q - sin θ`. At the zero state `V = 1`, the lift balances the unit
weight, and the drag and the horizontal actuator are `3/20`; the trim is a relative equilibrium:
the position moves as `p(t) = p₀ + (t, 0)`, not a stationary world position. On the box
`V ≥ 99/100`, `1/10 < A_x < 1/5`, `|A_z| < 1/20` and `|M| ≤ 3/100`, and a state of zero speed lies
outside it.

Model inputs (hypotheses of the module):

* the translational law `m X'' = R F_B + m g` and the rotational law `dL_COM/dt = R M_B`, with the
  body force `F_B` and the body moment `M_B` about the centre of mass, are assumed;
* the mass `m = M.mass` of the motion is positive, a hypothesis since Physlib's mass functional is
  an arbitrary linear functional, and constant, so no mass depletion is represented; the
  gravitational acceleration `g` is uniform;
* `R` (entry by entry) and the centre-of-mass trajectory (component by component) are `C²` on an
  open set of times; time derivatives are Physlib's `∂ₜ`;
* the rotational law takes a body frame centered at the centre of mass (`centerOfMass = 0`);
* the force and moment maps and their admitted domain are given;
* in section D, the synthetic lift, drag and polar, the ideal actuator laws and their admitted
  box are model inputs.

Non-goals: aerodynamic coefficient models other than the synthetic polar of section D, trim of
anything but the planar ideal-actuator fixture of section D, linearization, stability, existence
of trajectories for given maps (section D exhibits only the trim trajectory), and any empirical
adequacy or system safety claim.

## ii. Key results

- `bodyVelocity`, `differentiableAt_bodyVelocity` : the body velocity `v_B = Rᵀ X'` of the centre
  of mass, differentiable along `C²` data.
- `newton_iff_deriv_bodyVelocity` : `m X'' = R F_B + m g` holds exactly when
  `v_B' = F_B / m + Rᵀ g - ω_B × v_B`.
- `SixDofBodyEquations`, `balanceLaws_iff_sixDofBodyEquations` : the translational body equation
  paired with Euler's equations, equivalent to both inertial balance laws.
- `ForceMomentMaps`, `SixDofPlant`, `sixDofPlant_iff` : force and moment maps on an admitted
  domain, and the plant they define, which requires positive mass and `C²` data.
- `liftCoeff`, `dragCoeff`, `flightSpeed`, `liftForce`, `dragForce`, `aeroForce`,
  `actuatorForce`, `pitchMoment`, `dragCoeff_eq`, `liftForce_dragForce_spec`,
  `aeroForce_add_actuatorForce_add_weight` : the synthetic aerodynamics and the ideal actuators
  of the longitudinal fixture.
- `reducedField`, `actuatorBox`, `pitchOrientation`, `longitudinalMaps`, `planarMotion`,
  `planarState`, `planar_sixDofPlant_iff` : the plant restricted to planar motions is the reduced
  longitudinal system on the actuator box.
- `trim_relative_equilibrium`, `actuatorBox_bounds`, `longitudinalMaps_rejects` : the trim as a
  relative equilibrium, the actuator bounds on the box, and no evaluation outside it.

## iii. Table of contents

- A. Body velocity and the translational correspondence
- B. The six-degree-of-freedom body equations
- C. Coefficient maps with admitted domains
- D. A controlled longitudinal fixture

## iv. References

- B. L. Stevens, F. L. Lewis and E. N. Johnson, *Aircraft Control and Simulation*, 3rd edition,
  2016, chapter 1 (the rigid-body six-degree-of-freedom equations in body axes).
- B. Etkin, *Dynamics of Atmospheric Flight*, 1972 (the equations of motion in body axes and the
  longitudinal equations).
- J. D. Anderson, *Introduction to Flight*, McGraw-Hill (lift and drag coefficients and the
  parabolic drag polar `C_D = C_D0 + K C_L²`).
- L. D. Landau and E. M. Lifshitz, *Mechanics*, Sections 34 and 39 (the equations of motion of a
  rigid body; motion in a non-inertial frame of reference).
- `Mechanics.RigidMotionPorts` (the transport law `deriv_bodyToInertialVec` and the Euler
  equivalence `deriv_comAngularMomentum_eq_iff_euler`), Physlib's
  `RigidBodyMotion.bodyAngularVelocity` and
  `RigidBodyMotion.deriv_orientation_mulVec_eq_orientation_bodyAngularVelocity_cross`, and the
  frame dictionary `Units.EngineeringFrames`.
-/

@[expose] public section

open scoped Matrix
open Time

namespace Mechanics.FlightPlant

open Units.EngineeringFrames Mechanics.RigidMotionPorts

/-! ## A. Body velocity and the translational correspondence -/

/-- The body velocity `v_B = Rᵀ X'` of the motion `M`: the body components of the velocity `X'`
of its centre of mass, with `X` the inertial coordinates of the centre-of-mass trajectory and `R`
the orientation. -/
noncomputable def bodyVelocity (M : RigidBodyMotion 3) (t : Time) : Fin 3 → ℝ :=
  inertialToBodyVec (M.orientation t) (∂ₜ (fun s j => M.comTrajectory s j) t)

/-- Entrywise `C²` regularity of the orientation on an open set gives differentiability with the
default matrix instances. -/
private lemma differentiableAt_orientation_of_entries (M : RigidBodyMotion 3) {U : Set Time}
    (hU : IsOpen U) (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U)
    {t : Time} (ht : t ∈ U) : DifferentiableAt ℝ (fun s => (M.orientation s).1) t := by
  have h : DifferentiableAt ℝ (fun s => Matrix.of.symm (M.orientation s).1) t :=
    differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j =>
      ((hR i j).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)
  exact h

/-- The time derivative of a `C²` curve on an open set is differentiable there. -/
private lemma differentiableAt_deriv_of_two {X : Time → Fin 3 → ℝ} {U : Set Time}
    (hU : IsOpen U) (hX : ContDiffOn ℝ 2 X U) {t : Time} (ht : t ∈ U) :
    DifferentiableAt ℝ (∂ₜ X) t := by
  have h : ContDiffOn ℝ 1 (∂ₜ X) U :=
    (hX.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const
  exact (h.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)

/-- Along a motion whose orientation (entry by entry) and centre-of-mass trajectory (component by
component) are `C²` on an open set, the body velocity is differentiable, so `∂ₜ` of it is a
genuine derivative. -/
lemma differentiableAt_bodyVelocity (M : RigidBodyMotion 3) {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U)
    (hX : ∀ j, ContDiffOn ℝ 2 (fun s => M.comTrajectory s j) U) {t : Time} (ht : t ∈ U) :
    DifferentiableAt ℝ (bodyVelocity M) t := by
  have hXd := differentiableAt_deriv_of_two hU (contDiffOn_pi.2 hX) ht
  refine differentiableAt_pi.2 fun i => ?_
  simp only [bodyVelocity, inertialToBodyVec, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine DifferentiableAt.fun_sum fun j _ => ?_
  exact (((hR j i).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)).mul
    (differentiableAt_pi.1 hXd j)

/-- Translational correspondence: for a motion `M` of positive mass `m = M.mass` whose
orientation `R` (entry by entry) and centre-of-mass coordinates `X` are `C²` on an open set `U`, at
every `t ∈ U` the inertial law `m X'' = R F_B + m g` holds exactly when the body equation
`v_B' = F_B / m + Rᵀ g - ω_B × v_B` holds. -/
lemma newton_iff_deriv_bodyVelocity (M : RigidBodyMotion 3) {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U)
    (hX : ∀ j, ContDiffOn ℝ 2 (fun s => M.comTrajectory s j) U) (hm : 0 < M.mass)
    (FB g : Fin 3 → ℝ) {t : Time} (ht : t ∈ U) :
    M.mass • ∂ₜ (∂ₜ (fun s j => M.comTrajectory s j)) t =
        bodyToInertialVec (M.orientation t) FB + M.mass • g ↔
      ∂ₜ (bodyVelocity M) t = M.mass⁻¹ • FB + inertialToBodyVec (M.orientation t) g -
        M.bodyAngularVelocity t ⨯₃ bodyVelocity M t := by
  -- `X' = R v_B`, so the transport law of the rotating-frame module gives `X''`
  have hfun : ∂ₜ (fun s j => M.comTrajectory s j) =
      fun s => bodyToInertialVec (M.orientation s) (bodyVelocity M s) := by
    funext s
    exact (bodyToInertialVec_inertialToBodyVec (M.orientation s)
      (∂ₜ (fun s j => M.comTrajectory s j) s)).symm
  have htr := deriv_bodyToInertialVec M (bodyVelocity M) t
    (differentiableAt_orientation_of_entries M hU hR ht)
    (differentiableAt_bodyVelocity M hU hR hX ht)
  rw [hfun, htr]
  set m := M.mass
  set R := M.orientation t
  set a := ∂ₜ (bodyVelocity M) t
  set w := M.bodyAngularVelocity t ⨯₃ bodyVelocity M t
  have hm0 : m ≠ 0 := hm.ne'
  have key : ∀ x y : Fin 3 → ℝ, bodyToInertialVec R x = y ↔ x = inertialToBodyVec R y := by
    intro x y
    constructor
    · rintro rfl
      exact (inertialToBodyVec_bodyToInertialVec R x).symm
    · rintro rfl
      exact bodyToInertialVec_inertialToBodyVec R y
  have hsmul : m • bodyToInertialVec R (a + w) = bodyToInertialVec R (m • (a + w)) :=
    (Matrix.mulVec_smul _ m _).symm
  have hadd : ∀ x y, inertialToBodyVec R (x + y) = inertialToBodyVec R x + inertialToBodyVec R y :=
    fun x y => Matrix.mulVec_add _ x y
  have hsm : ∀ (c : ℝ) x, inertialToBodyVec R (c • x) = c • inertialToBodyVec R x :=
    fun c x => Matrix.mulVec_smul _ c x
  -- apply `Rᵀ` and divide by `m`
  rw [hsmul, key, hadd, hsm, inertialToBodyVec_bodyToInertialVec]
  constructor
  · intro h
    have h' : a + w = m⁻¹ • FB + inertialToBodyVec R g := by
      have h2 := congrArg (fun x => m⁻¹ • x) h
      simpa only [smul_add, smul_smul, inv_mul_cancel₀ hm0, one_smul] using h2
    exact eq_sub_of_add_eq h'
  · intro h
    rw [h, sub_add_cancel, smul_add, smul_smul, mul_inv_cancel₀ hm0, one_smul]

/-! ## B. The six-degree-of-freedom body equations -/

/-- The six-degree-of-freedom body equations of the motion `M` at time `t`, with its mass
`m = M.mass`, uniform gravity `g` (inertial components), body force `F_B` and body moment `M_B`
about the centre of mass: the translational equation `v_B' = F_B / m + Rᵀ g - ω_B × v_B` and
Euler's equations `I_B ω_B' + ω_B × (I_B ω_B) = M_B` of the rotating-frame module. -/
def SixDofBodyEquations (M : RigidBodyMotion 3) (g FB MB : Fin 3 → ℝ) (t : Time) : Prop :=
  ∂ₜ (bodyVelocity M) t = M.mass⁻¹ • FB + inertialToBodyVec (M.orientation t) g -
      M.bodyAngularVelocity t ⨯₃ bodyVelocity M t ∧
    M.inertiaTensorAbout M.centerOfMass *ᵥ ∂ₜ M.bodyAngularVelocity t +
        M.bodyAngularVelocity t ⨯₃
          (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity t) = MB

/-- The package with the reused rotation equation: for a motion of positive mass `m = M.mass`
whose orientation and centre-of-mass trajectory are `C²` on an open set `U`, with a body frame
centered at the centre of mass, at every `t ∈ U` the translational law `m X'' = R F_B + m g` and
the rotational law `dL_COM/dt = R M_B` both hold exactly when the six-degree-of-freedom body
equations hold. -/
lemma balanceLaws_iff_sixDofBodyEquations (M : RigidBodyMotion 3) {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U)
    (hX : ∀ j, ContDiffOn ℝ 2 (fun s => M.comTrajectory s j) U) (hc : M.centerOfMass = 0)
    (hm : 0 < M.mass) (g FB MB : Fin 3 → ℝ) {t : Time} (ht : t ∈ U) :
    (M.mass • ∂ₜ (∂ₜ (fun s j => M.comTrajectory s j)) t =
          bodyToInertialVec (M.orientation t) FB + M.mass • g ∧
        ∂ₜ (comAngularMomentum M) t = bodyToInertialVec (M.orientation t) MB) ↔
      SixDofBodyEquations M g FB MB t := by
  rw [newton_iff_deriv_bodyVelocity M hU hR hX hm FB g ht,
    deriv_comAngularMomentum_eq_iff_euler M hU hR hc ht, inertialToBodyVec_bodyToInertialVec]
  rfl

/-! ## C. Coefficient maps with admitted domains -/

/-- Aerodynamic and propulsive coefficient maps, explicit model inputs: the body force and the
body moment about the centre of mass as functions of a state in `S`, defined only on the admitted
domain (a polar validity region, for example), so they are never evaluated outside it. -/
structure ForceMomentMaps (S : Type*) where
  /-- The admitted states. -/
  domain : Set S
  /-- The body force at an admitted state. -/
  force : domain → Fin 3 → ℝ
  /-- The body moment about the centre of mass at an admitted state. -/
  moment : domain → Fin 3 → ℝ

/-- The six-degree-of-freedom plant of the motion `M` at time `t` along the state trajectory `x`,
the state the maps read: the motion has positive mass, its orientation (entry by entry) and its
centre-of-mass trajectory (component by component) are `C²` on an open set of times containing
`t`, the state is admitted, and the body equations hold with the force and the moment the maps give
there. Positive mass keeps the force in the translational equation, and the regularity makes the
derivatives in the body equations genuine. -/
def SixDofPlant {S : Type*} (c : ForceMomentMaps S) (x : Time → S) (M : RigidBodyMotion 3)
    (g : Fin 3 → ℝ) (t : Time) : Prop :=
  0 < M.mass ∧
    (∃ U : Set Time, IsOpen U ∧ t ∈ U ∧
      (∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) ∧
      ∀ j, ContDiffOn ℝ 2 (fun s => M.comTrajectory s j) U) ∧
    ∃ hx : x t ∈ c.domain, SixDofBodyEquations M g (c.force ⟨x t, hx⟩) (c.moment ⟨x t, hx⟩) t

/-- The coefficient-map domain wrapper: for a body frame centered at the centre of mass, the plant
holds at `t` exactly when the motion has positive mass and `C²` data on an open set of times
containing `t`, the state is admitted there, and both inertial balance laws hold with the force and
the moment the maps give at that state. -/
lemma sixDofPlant_iff {S : Type*} (c : ForceMomentMaps S) (x : Time → S) (M : RigidBodyMotion 3)
    (hc : M.centerOfMass = 0) (g : Fin 3 → ℝ) (t : Time) :
    SixDofPlant c x M g t ↔ 0 < M.mass ∧
      (∃ U : Set Time, IsOpen U ∧ t ∈ U ∧
        (∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) ∧
        ∀ j, ContDiffOn ℝ 2 (fun s => M.comTrajectory s j) U) ∧
      ∃ hx : x t ∈ c.domain,
        M.mass • ∂ₜ (∂ₜ (fun s j => M.comTrajectory s j)) t =
            bodyToInertialVec (M.orientation t) (c.force ⟨x t, hx⟩) + M.mass • g ∧
          ∂ₜ (comAngularMomentum M) t =
            bodyToInertialVec (M.orientation t) (c.moment ⟨x t, hx⟩) := by
  constructor
  · rintro ⟨hm, ⟨U, hU, ht, hR, hX⟩, hx, hbody⟩
    exact ⟨hm, ⟨U, hU, ht, hR, hX⟩, hx,
      (balanceLaws_iff_sixDofBodyEquations M hU hR hX hc hm g _ _ ht).mpr hbody⟩
  · rintro ⟨hm, ⟨U, hU, ht, hR, hX⟩, hx, hlaws⟩
    exact ⟨hm, ⟨U, hU, ht, hR, hX⟩, hx,
      (balanceLaws_iff_sixDofBodyEquations M hU hR hX hc hm g _ _ ht).mp hlaws⟩

/-! ## D. A controlled longitudinal fixture -/

/-- The lift coefficient of the fixture, `C_L = 2`. -/
def liftCoeff : ℝ := 2

/-- The drag polar of the fixture, `C_D = 1/10 + C_L² / 20`. -/
noncomputable def dragCoeff : ℝ := 1 / 10 + 1 / 20 * liftCoeff ^ 2

/-- The flight speed `V = √((1 + x)² + z²)` at the velocity `(1 + x, z)` of the forward/up
plane. -/
noncomputable def flightSpeed (x z : ℝ) : ℝ := Real.sqrt ((1 + x) ^ 2 + z ^ 2)

/-- The lift at the velocity `(1 + x, z, 0)` with unit air density and reference area: magnitude
`½ V² C_L`, along the velocity turned a quarter turn from forward toward up, written as
`½ V C_L (-z, 1 + x, 0)`. -/
noncomputable def liftForce (x z : ℝ) : Fin 3 → ℝ :=
  (flightSpeed x z * liftCoeff / 2) • ![-z, 1 + x, 0]

/-- The drag at the velocity `(1 + x, z, 0)` with unit air density and reference area: magnitude
`½ V² C_D`, against the velocity, written as `-½ V C_D (1 + x, z, 0)`. -/
noncomputable def dragForce (x z : ℝ) : Fin 3 → ℝ :=
  -(flightSpeed x z * dragCoeff / 2) • ![1 + x, z, 0]

/-- The aerodynamic force, lift plus drag, in inertial components. -/
noncomputable def aeroForce (x z : ℝ) : Fin 3 → ℝ := liftForce x z + dragForce x z

/-- The ideal vector force actuator `A = (-x - x³, 1 - z, 0) - F_aero`, an explicit part of the
model, in inertial components. -/
noncomputable def actuatorForce (x z : ℝ) : Fin 3 → ℝ :=
  ![-x - x ^ 3, 1 - z, 0] - aeroForce x z

/-- The pitch-moment actuator `M = -2 q - sin θ`. -/
noncomputable def pitchMoment (θ q : ℝ) : ℝ := -2 * q - Real.sin θ

/-- The reduced longitudinal field in the state order `(x, z, θ, q)`:
`(-x - x³, -z, q, -2 q - sin θ)`. -/
noncomputable def reducedField (e : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-e 0 - e 0 ^ 3, -e 1, e 3, -2 * e 3 - Real.sin (e 2)]

/-- The admitted actuator box: every state coordinate of `(x, z, θ, q)` at most `1/100` in
absolute value. -/
def actuatorBox : Set (Fin 4 → ℝ) := {e | ∀ i, |e i| ≤ 1 / 100}

/-- The pitch orientation `Rz(θ)`, the rotation by `θ` about the third axis. -/
noncomputable def pitchOrientation (θ : ℝ) : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨rotZ θ, rotZ_mem_specialOrthogonalGroup θ⟩

/-- The longitudinal force and moment maps on the admitted box, read on the state
`(x, z, θ, q)`: the body force `Rz(θ)ᵀ (F_aero + A)`, the aerodynamic and actuator force in body
components, and the body moment `(0, 0, M)` about the pitch axis. -/
noncomputable def longitudinalMaps : ForceMomentMaps (Fin 4 → ℝ) where
  domain := actuatorBox
  force := fun e => inertialToBodyVec (pitchOrientation (e.1 2))
    (aeroForce (e.1 0) (e.1 1) + actuatorForce (e.1 0) (e.1 1))
  moment := fun e => ![0, 0, pitchMoment (e.1 2) (e.1 3)]

/-- The planar longitudinal motion of the mass distribution `B`: the centre of mass at
`(X₁ t, X₂ t, 0)` in the forward/up plane and the pitch orientation `Rz(θ t)`. -/
noncomputable def planarMotion (B : RigidBody 3) (X₁ X₂ θ : Time → ℝ) : RigidBodyMotion 3 where
  toRigidBody := B
  comTrajectory := fun s => ⟨![X₁ s, X₂ s, 0]⟩
  orientation := fun s => pitchOrientation (θ s)

/-- The longitudinal state of the planar motion at time `t`: `x = X₁' - 1`, `z = X₂'`, the pitch
angle `θ` and the pitch rate `q = θ'`. -/
noncomputable def planarState (X₁ X₂ θ : Time → ℝ) (t : Time) : Fin 4 → ℝ :=
  ![∂ₜ X₁ t - 1, ∂ₜ X₂ t, θ t, ∂ₜ θ t]

/-- The drag polar gives `C_D = 3/10` at `C_L = 2`. -/
lemma dragCoeff_eq : dragCoeff = 3 / 10 := by
  unfold dragCoeff liftCoeff
  norm_num

/-- **Lift and drag.** At the velocity `v = (1 + x, z, 0)` the lift is perpendicular to `v`, has
squared magnitude `(V²)²` and points to the up side of `v`; the drag is `-(3 V / 20) v`, against
`v`, with squared magnitude `(3 V² / 20)²`. -/
lemma liftForce_dragForce_spec (x z : ℝ) :
    liftForce x z ⬝ᵥ ![1 + x, z, 0] = 0 ∧
      liftForce x z ⬝ᵥ liftForce x z = (flightSpeed x z ^ 2) ^ 2 ∧
      0 ≤ liftForce x z ⬝ᵥ ![-z, 1 + x, 0] ∧
      dragForce x z = -(3 / 20 * flightSpeed x z) • ![1 + x, z, 0] ∧
      dragForce x z ⬝ᵥ dragForce x z = (3 / 20 * flightSpeed x z ^ 2) ^ 2 := by
  have hV2 : flightSpeed x z ^ 2 = (1 + x) ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)
  have hV0 : 0 ≤ flightSpeed x z := Real.sqrt_nonneg _
  have hL : liftForce x z = flightSpeed x z • ![-z, 1 + x, 0] := by
    unfold liftForce liftCoeff
    congr 1
    ring
  have hDr : dragForce x z = -(3 / 20 * flightSpeed x z) • ![1 + x, z, 0] := by
    unfold dragForce
    rw [dragCoeff_eq]
    congr 1
    ring
  refine ⟨?_, ?_, ?_, hDr, ?_⟩
  · rw [hL]
    simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  · rw [hL]
    simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (-(flightSpeed x z ^ 2)) * hV2
  · rw [hL]
    simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have : 0 ≤ flightSpeed x z * ((1 + x) ^ 2 + z ^ 2) := by positivity
    nlinarith
  · rw [hDr]
    simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (-(9 / 400 * flightSpeed x z ^ 2)) * hV2

/-- **The force balance.** The aerodynamic force, the actuator force and the weight
`(0, -1, 0)` add up to `(-x - x³, -z, 0)`. -/
lemma aeroForce_add_actuatorForce_add_weight (x z : ℝ) :
    aeroForce x z + actuatorForce x z + ![0, -1, 0] = ![-x - x ^ 3, -z, 0] := by
  ext i
  fin_cases i <;> simp [actuatorForce]
  ring

/-- The time derivative of a vector-valued curve differentiable at `t` is taken component by
component. -/
private lemma deriv_apply_of_differentiableAt {n : ℕ} {f : Time → Fin n → ℝ} {t : Time}
    (hf : DifferentiableAt ℝ f t) (i : Fin n) : ∂ₜ (fun s => f s i) t = ∂ₜ f t i := by
  have h : HasFDerivAt (fun s => f s i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp (fderiv ℝ f t)) t :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt.comp t
      hf.hasFDerivAt
  rw [Time.deriv_eq, h.fderiv, Time.deriv_eq]
  rfl

/-- The time derivative of a curve `s ↦ (a s, b s, c s)` with components differentiable at `t`. -/
private lemma deriv_vec3 {a b c : Time → ℝ} {t : Time} (ha : DifferentiableAt ℝ a t)
    (hb : DifferentiableAt ℝ b t) (hc : DifferentiableAt ℝ c t) :
    ∂ₜ (fun s => ![a s, b s, c s]) t = ![∂ₜ a t, ∂ₜ b t, ∂ₜ c t] := by
  have hd : DifferentiableAt ℝ (fun s => ![a s, b s, c s]) t := by
    refine differentiableAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using ha
    · simpa using hb
    · simpa using hc
  funext i
  rw [← deriv_apply_of_differentiableAt hd i]
  fin_cases i
  · rfl
  · rfl
  · rfl

/-- The chain rule for `cos ∘ θ` and `sin ∘ θ` with the time derivative. -/
private lemma deriv_cos_sin_comp {θ : Time → ℝ} {t : Time} (hθ : DifferentiableAt ℝ θ t) :
    ∂ₜ (fun s => Real.cos (θ s)) t = ∂ₜ θ t * -Real.sin (θ t) ∧
      ∂ₜ (fun s => Real.sin (θ s)) t = ∂ₜ θ t * Real.cos (θ t) ∧
      ∂ₜ (fun s => -Real.sin (θ s)) t = ∂ₜ θ t * -Real.cos (θ t) := by
  have h := Time.hasDerivAt_mk_of_differentiableAt hθ
  refine ⟨?_, ?_, ?_⟩
  · exact Time.deriv_eq_of_hasDerivAt (((Real.hasDerivAt_cos _).comp t.val h).congr_deriv
      (by ring))
  · exact Time.deriv_eq_of_hasDerivAt (((Real.hasDerivAt_sin _).comp t.val h).congr_deriv
      (by ring))
  · exact Time.deriv_eq_of_hasDerivAt (((Real.hasDerivAt_sin _).comp t.val h).neg.congr_deriv
      (by ring))

/-- The pitch orientation along a curve differentiable at `t` is differentiable at `t`. -/
private lemma differentiableAt_rotZ_comp {θ : Time → ℝ} {t : Time}
    (hθ : DifferentiableAt ℝ θ t) : DifferentiableAt ℝ (fun s => rotZ (θ s)) t := by
  have hc : DifferentiableAt ℝ (fun s => Real.cos (θ s)) t := Real.differentiableAt_cos.comp t hθ
  have hs : DifferentiableAt ℝ (fun s => Real.sin (θ s)) t := Real.differentiableAt_sin.comp t hθ
  have h : DifferentiableAt ℝ (fun s => Matrix.of.symm (rotZ (θ s))) t := by
    refine differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => ?_
    fin_cases i <;> fin_cases j <;> simp only [rotZ] <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
        Matrix.cons_val_fin_one, Equiv.symm_apply_apply] <;>
      first
        | exact hc
        | exact hs
        | exact hs.neg
        | exact differentiableAt_const _
  exact h

/-- The pitch orientation has the derivative `θ' dRz/dθ`. -/
private lemma deriv_rotZ_comp {θ : Time → ℝ} {t : Time} (hθ : DifferentiableAt ℝ θ t) :
    ∂ₜ (fun s => rotZ (θ s)) t = ∂ₜ θ t •
      !![-Real.sin (θ t), -Real.cos (θ t), 0; Real.cos (θ t), -Real.sin (θ t), 0; 0, 0, 0] := by
  obtain ⟨dc, ds, dns⟩ := deriv_cos_sin_comp hθ
  ext i j
  refine (Time.deriv_matrix_apply _ t (differentiableAt_rotZ_comp hθ) i j).symm.trans ?_
  fin_cases i <;> fin_cases j <;> simp only [rotZ] <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.smul_apply, smul_eq_mul] <;>
    first
      | exact dc
      | exact ds
      | exact dns
      | simp

/-- The body angular velocity of the planar motion is `(0, 0, θ')`. -/
private lemma planarMotion_bodyAngularVelocity (B : RigidBody 3) (X₁ X₂ : Time → ℝ)
    {θ : Time → ℝ} {t : Time} (hθ : DifferentiableAt ℝ θ t) :
    (planarMotion B X₁ X₂ θ).bodyAngularVelocity t = ![0, 0, ∂ₜ θ t] := by
  have h : (planarMotion B X₁ X₂ θ).bodyAngularVelocity t = Matrix.crossProductVee
      ((((planarMotion B X₁ X₂ θ).orientation t : Matrix (Fin 3) (Fin 3) ℝ))ᵀ *
        ∂ₜ (fun s => ((planarMotion B X₁ X₂ θ).orientation s).1) t) := rfl
  have hR : (((planarMotion B X₁ X₂ θ).orientation t : Matrix (Fin 3) (Fin 3) ℝ)) =
      rotZ (θ t) := rfl
  have hRf : (fun s => ((planarMotion B X₁ X₂ θ).orientation s).1) = fun s => rotZ (θ s) := rfl
  rw [h, hRf, deriv_rotZ_comp hθ, hR]
  have hcs := Real.cos_sq_add_sin_sq (θ t)
  ext i
  fin_cases i
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ∂ₜ θ t * hcs

/-- **Restriction of the plant to the plane.** For a mass distribution of mass `1` with centre of
mass `0` and inertia `diag(I_xx, I_yy, 1)` about it (pitch inertia `1` about the principal third
axis), and `C²` coordinates `X₁`, `X₂` and pitch angle `θ`, the six-degree-of-freedom plant of
the planar motion with the longitudinal maps and gravity `(0, -1, 0)` holds at `t` exactly when
the state is in the actuator box and its rate is the reduced field:
`x' = -x - x³`, `z' = -z`, `θ' = q`, `q' = -2 q - sin θ`. -/
lemma planar_sixDofPlant_iff (B : RigidBody 3) (hm : B.mass = 1) (hc : B.centerOfMass = 0)
    {Ixx Iyy : ℝ} (hI : B.inertiaTensorAbout B.centerOfMass = Matrix.diagonal ![Ixx, Iyy, 1])
    {X₁ X₂ θ : Time → ℝ} (hX₁ : ContDiff ℝ 2 X₁) (hX₂ : ContDiff ℝ 2 X₂) (hθ : ContDiff ℝ 2 θ)
    (t : Time) :
    SixDofPlant longitudinalMaps (planarState X₁ X₂ θ) (planarMotion B X₁ X₂ θ) ![0, -1, 0] t ↔
      planarState X₁ X₂ θ t ∈ actuatorBox ∧
        (fun i => ∂ₜ (fun s => planarState X₁ X₂ θ s i) t) =
          reducedField (planarState X₁ X₂ θ t) := by
  have hd1 : Differentiable ℝ X₁ := hX₁.differentiable (by norm_num)
  have hd2 : Differentiable ℝ X₂ := hX₂.differentiable (by norm_num)
  have hdθ : Differentiable ℝ θ := hθ.differentiable (by norm_num)
  have hdd1 : Differentiable ℝ (∂ₜ X₁) := deriv_differentiable_of_contDiff_two X₁ hX₁
  have hdd2 : Differentiable ℝ (∂ₜ X₂) := deriv_differentiable_of_contDiff_two X₂ hX₂
  have hddθ : Differentiable ℝ (∂ₜ θ) := deriv_differentiable_of_contDiff_two θ hθ
  have hR : ∀ i j, ContDiffOn ℝ 2 (fun s => ((planarMotion B X₁ X₂ θ).orientation s).1 i j)
      Set.univ := by
    intro i j
    have hc := (Real.contDiff_cos.comp hθ).contDiffOn (s := Set.univ)
    have hs := (Real.contDiff_sin.comp hθ).contDiffOn (s := Set.univ)
    fin_cases i <;> fin_cases j <;> simp only [planarMotion, pitchOrientation, rotZ] <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
        Matrix.cons_val_fin_one] <;>
      first
        | exact hc
        | exact hs
        | exact hs.neg
        | exact contDiffOn_const
  have hX : ∀ j, ContDiffOn ℝ 2 (fun s => (planarMotion B X₁ X₂ θ).comTrajectory s j)
      Set.univ := by
    intro j
    fin_cases j
    · exact hX₁.contDiffOn
    · exact hX₂.contDiffOn
    · exact contDiffOn_const
  have hc' : (planarMotion B X₁ X₂ θ).centerOfMass = 0 := hc
  have hm' : (planarMotion B X₁ X₂ θ).mass = 1 := hm
  have hI' : (planarMotion B X₁ X₂ θ).inertiaTensorAbout (planarMotion B X₁ X₂ θ).centerOfMass =
      Matrix.diagonal ![Ixx, Iyy, 1] := hI
  have hvel : ∂ₜ (fun s j => (planarMotion B X₁ X₂ θ).comTrajectory s j) =
      fun s => ![∂ₜ X₁ s, ∂ₜ X₂ s, 0] := by
    funext s
    have h := deriv_vec3 (hd1 s) (hd2 s) (differentiableAt_const (0 : ℝ))
    rw [Time.deriv_const] at h
    exact h
  have hacc : ∂ₜ (∂ₜ (fun s j => (planarMotion B X₁ X₂ θ).comTrajectory s j)) t =
      ![∂ₜ (∂ₜ X₁) t, ∂ₜ (∂ₜ X₂) t, 0] := by
    rw [hvel]
    have h := deriv_vec3 (hdd1 t) (hdd2 t) (differentiableAt_const (0 : ℝ))
    rw [Time.deriv_const] at h
    exact h
  have hω : ∀ s, (planarMotion B X₁ X₂ θ).bodyAngularVelocity s = ![0, 0, ∂ₜ θ s] :=
    fun s => planarMotion_bodyAngularVelocity B X₁ X₂ (hdθ s)
  have hω' : ∂ₜ (planarMotion B X₁ X₂ θ).bodyAngularVelocity t = ![0, 0, ∂ₜ (∂ₜ θ) t] := by
    rw [show (planarMotion B X₁ X₂ θ).bodyAngularVelocity = fun s => ![0, 0, ∂ₜ θ s] from
      funext hω]
    have h := deriv_vec3 (differentiableAt_const (0 : ℝ)) (differentiableAt_const (0 : ℝ))
      (hddθ t) (t := t)
    rw [Time.deriv_const] at h
    exact h
  have hstate : (fun i => ∂ₜ (fun s => planarState X₁ X₂ θ s i) t) =
      ![∂ₜ (∂ₜ X₁) t, ∂ₜ (∂ₜ X₂) t, ∂ₜ θ t, ∂ₜ (∂ₜ θ) t] := by
    funext i
    fin_cases i
    · change ∂ₜ (fun s => ∂ₜ X₁ s - 1) t = ∂ₜ (∂ₜ X₁) t
      exact Time.deriv_eq_of_hasDerivAt
        ((Time.hasDerivAt_mk_of_differentiableAt (hdd1 t)).sub_const 1)
    · rfl
    · rfl
    · rfl
  have hF : ∀ hx : planarState X₁ X₂ θ t ∈ longitudinalMaps.domain,
      bodyToInertialVec ((planarMotion B X₁ X₂ θ).orientation t)
          (longitudinalMaps.force ⟨planarState X₁ X₂ θ t, hx⟩) =
        ![-(∂ₜ X₁ t - 1) - (∂ₜ X₁ t - 1) ^ 3, 1 - ∂ₜ X₂ t, 0] := by
    intro hx
    change bodyToInertialVec (pitchOrientation (θ t)) (inertialToBodyVec (pitchOrientation (θ t))
      (aeroForce (∂ₜ X₁ t - 1) (∂ₜ X₂ t) + actuatorForce (∂ₜ X₁ t - 1) (∂ₜ X₂ t))) = _
    rw [bodyToInertialVec_inertialToBodyVec]
    unfold actuatorForce
    abel
  have hMB : ∀ hx : planarState X₁ X₂ θ t ∈ longitudinalMaps.domain,
      longitudinalMaps.moment ⟨planarState X₁ X₂ θ t, hx⟩ =
        ![0, 0, pitchMoment (θ t) (∂ₜ θ t)] := fun _ => rfl
  have heuler : ∀ τ : Fin 3 → ℝ,
      ∂ₜ (comAngularMomentum (planarMotion B X₁ X₂ θ)) t =
          bodyToInertialVec ((planarMotion B X₁ X₂ θ).orientation t) τ ↔
        ![0, 0, ∂ₜ (∂ₜ θ) t] = τ := by
    intro τ
    rw [deriv_comAngularMomentum_eq_iff_euler _ isOpen_univ hR hc' (Set.mem_univ t),
      inertialToBodyVec_bodyToInertialVec, hI', hω t, hω']
    have hlhs : Matrix.diagonal ![Ixx, Iyy, 1] *ᵥ ![0, 0, ∂ₜ (∂ₜ θ) t] +
        ![0, 0, ∂ₜ θ t] ⨯₃ (Matrix.diagonal ![Ixx, Iyy, 1] *ᵥ ![0, 0, ∂ₜ θ t]) =
          ![0, 0, ∂ₜ (∂ₜ θ) t] := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec_diagonal, cross_apply]
    rw [hlhs]
  rw [sixDofPlant_iff longitudinalMaps _ (planarMotion B X₁ X₂ θ) hc' _ t, hstate]
  constructor
  · rintro ⟨-, -, hx, hlaw, hang⟩
    refine ⟨hx, ?_⟩
    rw [hF hx, hm', one_smul, one_smul, hacc] at hlaw
    rw [hMB hx, heuler] at hang
    have h0 := congrFun hlaw 0
    have h1 := congrFun hlaw 1
    have h3 := congrFun hang 2
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, neg_sub,
      Pi.add_apply, add_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h3
    unfold pitchMoment at h3
    funext i
    fin_cases i
    · simp [reducedField, planarState]
      linarith
    · simp [reducedField, planarState]
      linarith
    · simp [reducedField, planarState]
    · simp [reducedField, planarState]
      linarith
  · rintro ⟨hx, hred⟩
    have h0 := congrFun hred 0
    have h1 := congrFun hred 1
    have h3 := congrFun hred 3
    simp [reducedField, planarState] at h0 h1 h3
    refine ⟨by rw [hm']; norm_num, ⟨Set.univ, isOpen_univ, Set.mem_univ t, hR, hX⟩, hx, ?_, ?_⟩
    · rw [hF hx, hm', one_smul, one_smul, hacc]
      ext i
      fin_cases i
      · simp
        linarith
      · simp
        linarith
      · simp
    · rw [hMB hx, heuler]
      ext i
      fin_cases i
      · simp
      · simp
      · simp [pitchMoment]
        linarith

/-- **The trim is a relative equilibrium.** For a mass distribution as in
`planar_sixDofPlant_iff`, the planar motion with position `p(t) = (p₁ + t, p₂)` and zero pitch has
zero longitudinal state and is a plant solution at every time, while its centre of mass moves
with the nonzero rate `(1, 0, 0)`: not a stationary world-position state. -/
lemma trim_relative_equilibrium (B : RigidBody 3) (hm : B.mass = 1) (hc : B.centerOfMass = 0)
    {Ixx Iyy : ℝ} (hI : B.inertiaTensorAbout B.centerOfMass = Matrix.diagonal ![Ixx, Iyy, 1])
    (p₁ p₂ : ℝ) (t : Time) :
    planarState (fun s => p₁ + s.val) (fun _ => p₂) (fun _ => 0) t = 0 ∧
      SixDofPlant longitudinalMaps (planarState (fun s => p₁ + s.val) (fun _ => p₂) (fun _ => 0))
        (planarMotion B (fun s => p₁ + s.val) (fun _ => p₂) (fun _ => 0)) ![0, -1, 0] t ∧
      ∂ₜ (fun s j => (planarMotion B (fun s => p₁ + s.val) (fun _ => p₂) (fun _ => 0)).comTrajectory
        s j) t = ![1, 0, 0] := by
  have hX₁ : ContDiff ℝ 2 (fun s : Time => p₁ + s.val) := contDiff_const.add Time.val_contDiff
  have hX₂ : ContDiff ℝ 2 (fun _ : Time => p₂) := contDiff_const
  have hθ : ContDiff ℝ 2 (fun _ : Time => (0 : ℝ)) := contDiff_const
  have hrate : ∀ s : Time, ∂ₜ (fun s : Time => p₁ + s.val) s = 1 := fun s =>
    Time.deriv_eq_of_hasDerivAt (by simpa using (hasDerivAt_id s.val).const_add p₁)
  have hstate : ∀ s, planarState (fun s => p₁ + s.val) (fun _ => p₂) (fun _ => 0) s = 0 := by
    intro s
    ext i
    fin_cases i <;> simp [planarState, hrate]
  refine ⟨hstate t, ?_, ?_⟩
  · rw [planar_sixDofPlant_iff B hm hc hI hX₁ hX₂ hθ t]
    refine ⟨by rw [hstate t]; intro i; simp, ?_⟩
    rw [hstate t]
    funext i
    have h : (fun s => planarState (fun s => p₁ + s.val) (fun _ => p₂) (fun _ => 0) s i) =
        fun _ => 0 := by
      funext s
      rw [hstate s]
      rfl
    rw [h, Time.deriv_const]
    fin_cases i <;> simp [reducedField]
  · have hd : DifferentiableAt ℝ (fun s : Time => p₁ + s.val) t :=
      (hX₁.differentiable (by norm_num)) t
    have h := deriv_vec3 hd (differentiableAt_const p₂) (differentiableAt_const (0 : ℝ))
    rw [hrate, Time.deriv_const, Time.deriv_const] at h
    exact h

/-- **Actuator domain.** On the box: `V ≥ 99/100`, `1/10 < A_x < 1/5`, `|A_z| < 1/20` and
`|M| ≤ 3/100`. -/
lemma actuatorBox_bounds {e : Fin 4 → ℝ} (he : e ∈ actuatorBox) :
    99 / 100 ≤ flightSpeed (e 0) (e 1) ∧ 1 / 10 < actuatorForce (e 0) (e 1) 0 ∧
      actuatorForce (e 0) (e 1) 0 < 1 / 5 ∧ |actuatorForce (e 0) (e 1) 1| < 1 / 20 ∧
      |pitchMoment (e 2) (e 3)| ≤ 3 / 100 := by
  have hx := he 0
  have hz := he 1
  have hθ := he 2
  have hq := he 3
  set x := e 0
  set z := e 1
  have hV2 : flightSpeed x z ^ 2 = (1 + x) ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)
  have hV0 : 0 ≤ flightSpeed x z := Real.sqrt_nonneg _
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  have hVlo : 99 / 100 ≤ flightSpeed x z := by nlinarith [sq_nonneg z]
  have hVhi : flightSpeed x z ≤ 10101 / 10000 := by nlinarith [sq_nonneg z]
  have hx3 : |x ^ 3| ≤ 1 / 1000000 := by
    rw [abs_pow]
    calc |x| ^ 3 ≤ (1 / 100) ^ 3 := pow_le_pow_left₀ (abs_nonneg x) hx 3
      _ = 1 / 1000000 := by norm_num
  obtain ⟨hx31, hx32⟩ := abs_le.mp hx3
  have hD : dragCoeff = 3 / 10 := dragCoeff_eq
  have hAx : actuatorForce x z 0 =
      -x - x ^ 3 + flightSpeed x z * (z + 3 / 20 * (1 + x)) := by
    simp [actuatorForce, aeroForce, liftForce, dragForce, hD, liftCoeff]
    ring
  have hAz : actuatorForce x z 1 =
      1 - z - flightSpeed x z * (1 + x) + 3 / 20 * (flightSpeed x z * z) := by
    simp [actuatorForce, aeroForce, liftForce, dragForce, hD, liftCoeff]
    ring
  have hw1 : 1385 / 10000 ≤ z + 3 / 20 * (1 + x) := by linarith
  have hw2 : z + 3 / 20 * (1 + x) ≤ 1615 / 10000 := by linarith
  have hVw1 : 99 / 100 * (1385 / 10000) ≤ flightSpeed x z * (z + 3 / 20 * (1 + x)) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hVlo) (by linarith : (0 : ℝ) ≤ z + 3 / 20 * (1 + x))]
  have hVw2 : flightSpeed x z * (z + 3 / 20 * (1 + x)) ≤ 10101 / 10000 * (1615 / 10000) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hVhi) (by linarith : (0 : ℝ) ≤ z + 3 / 20 * (1 + x))]
  have hVx1 : 99 / 100 * (99 / 100) ≤ flightSpeed x z * (1 + x) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hVlo) (by linarith : (0 : ℝ) ≤ 1 + x)]
  have hVx2 : flightSpeed x z * (1 + x) ≤ 10101 / 10000 * (101 / 100) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hVhi) (by linarith : (0 : ℝ) ≤ 1 + x)]
  have hVz : |flightSpeed x z * z| ≤ 10101 / 10000 * (1 / 100) := by
    rw [abs_mul, abs_of_nonneg hV0]
    exact mul_le_mul hVhi hz (abs_nonneg z) (by norm_num)
  obtain ⟨hVz1, hVz2⟩ := abs_le.mp hVz
  refine ⟨hVlo, ?_, ?_, ?_, ?_⟩
  · rw [hAx]
    linarith
  · rw [hAx]
    linarith
  · rw [hAz, abs_lt]
    constructor <;> linarith
  · unfold pitchMoment
    have hs : |Real.sin (e 2)| ≤ |e 2| := Real.abs_sin_le_abs
    calc |-2 * e 3 - Real.sin (e 2)| ≤ |-2 * e 3| + |Real.sin (e 2)| := abs_sub _ _
      _ ≤ 2 * (1 / 100) + 1 / 100 := by
        rw [abs_mul]
        norm_num
        linarith
      _ = 3 / 100 := by norm_num

/-- **No evaluation outside the box.** A state of zero speed is outside the box, and at a state
outside the box the plant fails, whatever the motion and the gravity. -/
lemma longitudinalMaps_rejects {x : Time → Fin 4 → ℝ} (M : RigidBodyMotion 3) (g : Fin 3 → ℝ)
    (t : Time) :
    (flightSpeed (x t 0) (x t 1) = 0 → x t ∉ actuatorBox) ∧
      (x t ∉ actuatorBox → ¬ SixDofPlant longitudinalMaps x M g t) := by
  refine ⟨fun h0 hx => ?_, fun hx hplant => ?_⟩
  · have := (actuatorBox_bounds hx).1
    rw [h0] at this
    norm_num at this
  · obtain ⟨-, -, hx', -⟩ := hplant
    exact hx hx'

end Mechanics.FlightPlant
