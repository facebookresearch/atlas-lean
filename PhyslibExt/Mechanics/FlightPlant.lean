/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.RigidMotionPorts

/-!
# Six-degree-of-freedom flight plant: the translational port with the shared rotation

The body-axis translational equation of a rigid motion's centre of mass, derived from the
rotating-frame transport law, paired with the existing Euler equations of the same motion, and the
plant defined by aerodynamic and propulsive force and moment maps on an admitted domain.

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
never evaluated elsewhere. The plant holds at a time exactly when the state is admitted there and
the inertial laws hold with the force and the moment the maps give.

Model inputs (hypotheses of the module):

* the translational law `m X'' = R F_B + m g` and the rotational law `dL_COM/dt = R M_B`, with the
  body force `F_B` and the body moment `M_B` about the centre of mass, are assumed;
* the mass `m = M.mass` of the motion is positive, a hypothesis since Physlib's mass functional is
  an arbitrary linear functional, and constant, so no mass depletion is represented; the
  gravitational acceleration `g` is uniform;
* `R` (entry by entry) and the centre-of-mass trajectory (component by component) are `C²` on an
  open set of times; time derivatives are Physlib's `∂ₜ`;
* the rotational law takes a body frame centered at the centre of mass (`centerOfMass = 0`);
* the force and moment maps and their admitted domain are given.

Non-goals: aerodynamic coefficient models, trim, linearization, stability, existence of
trajectories for given maps, and any empirical adequacy or system safety claim.

## ii. Key results

- `bodyVelocity`, `differentiableAt_bodyVelocity` : the body velocity `v_B = Rᵀ X'` of the centre
  of mass, differentiable along `C²` data.
- `newton_iff_deriv_bodyVelocity` : `m X'' = R F_B + m g` holds exactly when
  `v_B' = F_B / m + Rᵀ g - ω_B × v_B`.
- `SixDofBodyEquations`, `balanceLaws_iff_sixDofBodyEquations` : the translational body equation
  paired with Euler's equations, equivalent to both inertial balance laws.
- `ForceMomentMaps`, `SixDofPlant`, `sixDofPlant_iff` : force and moment maps on an admitted
  domain, and the plant they define.

## iii. Table of contents

- A. Body velocity and the translational correspondence
- B. The six-degree-of-freedom body equations
- C. Coefficient maps with admitted domains

## iv. References

- B. L. Stevens, F. L. Lewis and E. N. Johnson, *Aircraft Control and Simulation*, 3rd edition,
  2016, chapter 1 (the rigid-body six-degree-of-freedom equations in body axes).
- B. Etkin, *Dynamics of Atmospheric Flight*, 1972 (the equations of motion in body axes).
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
the state the maps read: the state is admitted, and the body equations hold with the force and the
moment the maps give there. -/
def SixDofPlant {S : Type*} (c : ForceMomentMaps S) (x : Time → S) (M : RigidBodyMotion 3)
    (g : Fin 3 → ℝ) (t : Time) : Prop :=
  ∃ hx : x t ∈ c.domain, SixDofBodyEquations M g (c.force ⟨x t, hx⟩) (c.moment ⟨x t, hx⟩) t

/-- The coefficient-map domain wrapper: under the hypotheses of the package, the plant holds at
`t ∈ U` exactly when the state is admitted there and both inertial balance laws hold with the
force and the moment the maps give at that state. -/
lemma sixDofPlant_iff {S : Type*} (c : ForceMomentMaps S) (x : Time → S) (M : RigidBodyMotion 3)
    {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U)
    (hX : ∀ j, ContDiffOn ℝ 2 (fun s => M.comTrajectory s j) U) (hc : M.centerOfMass = 0)
    (hm : 0 < M.mass) (g : Fin 3 → ℝ) {t : Time} (ht : t ∈ U) :
    SixDofPlant c x M g t ↔ ∃ hx : x t ∈ c.domain,
      M.mass • ∂ₜ (∂ₜ (fun s j => M.comTrajectory s j)) t =
          bodyToInertialVec (M.orientation t) (c.force ⟨x t, hx⟩) + M.mass • g ∧
        ∂ₜ (comAngularMomentum M) t = bodyToInertialVec (M.orientation t) (c.moment ⟨x t, hx⟩) := by
  exact exists_congr fun _ =>
    (balanceLaws_iff_sixDofBodyEquations M hU hR hX hc hm g _ _ ht).symm

end Mechanics.FlightPlant
