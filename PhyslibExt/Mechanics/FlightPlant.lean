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

The body-axis translational equation of a rigid vehicle of constant mass, derived from the
rotating-frame transport law, paired with the existing Euler equations, and the plant defined by
aerodynamic and propulsive force and moment maps on an admitted domain.

## i. Overview

A rigid vehicle of constant mass `m > 0` has its centre of mass at the inertial position `X(t)`
and the orientation `R(t) ∈ SO(3)` of a Physlib `RigidBodyMotion`, with the body-to-inertial
convention `v_I = R v_B` of `Units.EngineeringFrames`. The body velocity is `v_B = Rᵀ X'`, the
inertial velocity in body components, and `ω_B` is Physlib's body angular velocity, the vee of
`Rᵀ Ṙ`.

The translational balance law `m X'' = R F_B + m g` is a model input: `F_B` is the aerodynamic and
propulsive force in body components and `g` the uniform gravitational acceleration in inertial
components. Since `X' = R v_B`, the transport law `d(R u)/dt = R (u' + ω_B × u)` of
`Mechanics.RigidMotionPorts` gives `X'' = R (v_B' + ω_B × v_B)`, and for a `C²` position and
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
* the mass `m > 0` is constant, so no mass depletion is represented, and the gravitational
  acceleration `g` is uniform;
* `R` (entry by entry) and `X` are `C²` on an open set of times; time derivatives are Physlib's
  `∂ₜ`;
* the rotational law takes a body frame centered at the centre of mass (`centerOfMass = 0`);
* the force and moment maps and their admitted domain are given.

Non-goals: aerodynamic coefficient models, trim, linearization, stability, existence of
trajectories for given maps, and any empirical adequacy or system safety claim.

## ii. Key results

- `bodyVelocity`, `differentiableAt_bodyVelocity` : the body velocity `v_B = Rᵀ X'`,
  differentiable along `C²` data.
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

/-- The body velocity `v_B = Rᵀ X'`: the body components of the inertial velocity `X'` of the
position `X`, with `R` the orientation of the motion `M`. -/
noncomputable def bodyVelocity (M : RigidBodyMotion 3) (X : Time → Fin 3 → ℝ) (t : Time) :
    Fin 3 → ℝ :=
  inertialToBodyVec (M.orientation t) (∂ₜ X t)

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

/-- Along a `C²` position and orientation the body velocity is differentiable, so `∂ₜ` of it is a
genuine derivative. -/
lemma differentiableAt_bodyVelocity (M : RigidBodyMotion 3) (X : Time → Fin 3 → ℝ)
    {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) (hX : ContDiffOn ℝ 2 X U)
    {t : Time} (ht : t ∈ U) : DifferentiableAt ℝ (bodyVelocity M X) t := by
  have hXd := differentiableAt_deriv_of_two hU hX ht
  refine differentiableAt_pi.2 fun i => ?_
  simp only [bodyVelocity, inertialToBodyVec, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine DifferentiableAt.fun_sum fun j _ => ?_
  exact (((hR j i).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)).mul
    (differentiableAt_pi.1 hXd j)

/-- Translational correspondence: for constant mass `m > 0`, a position `X` and an orientation
`R` of class `C²` on an open set `U`, at every `t ∈ U` the inertial law `m X'' = R F_B + m g`
holds exactly when the body equation `v_B' = F_B / m + Rᵀ g - ω_B × v_B` holds. -/
lemma newton_iff_deriv_bodyVelocity (M : RigidBodyMotion 3) (X : Time → Fin 3 → ℝ)
    {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) (hX : ContDiffOn ℝ 2 X U)
    {m : ℝ} (hm : 0 < m) (FB g : Fin 3 → ℝ) {t : Time} (ht : t ∈ U) :
    m • ∂ₜ (∂ₜ X) t = bodyToInertialVec (M.orientation t) FB + m • g ↔
      ∂ₜ (bodyVelocity M X) t = m⁻¹ • FB + inertialToBodyVec (M.orientation t) g -
        M.bodyAngularVelocity t ⨯₃ bodyVelocity M X t := by
  -- `X' = R v_B`, so the transport law of the rotating-frame module gives `X''`
  have hfun : ∂ₜ X = fun s => bodyToInertialVec (M.orientation s) (bodyVelocity M X s) := by
    funext s
    exact (bodyToInertialVec_inertialToBodyVec (M.orientation s) (∂ₜ X s)).symm
  have htr := deriv_bodyToInertialVec M (bodyVelocity M X) t
    (differentiableAt_orientation_of_entries M hU hR ht)
    (differentiableAt_bodyVelocity M X hU hR hX ht)
  rw [hfun, htr]
  set R := M.orientation t
  set a := ∂ₜ (bodyVelocity M X) t
  set w := M.bodyAngularVelocity t ⨯₃ bodyVelocity M X t
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

/-- The six-degree-of-freedom body equations at time `t` for constant mass `m`, uniform gravity
`g` (inertial components), body force `F_B` and body moment `M_B` about the centre of mass: the
translational equation `v_B' = F_B / m + Rᵀ g - ω_B × v_B` and Euler's equations
`I_B ω_B' + ω_B × (I_B ω_B) = M_B` of the rotating-frame module. -/
def SixDofBodyEquations (M : RigidBodyMotion 3) (X : Time → Fin 3 → ℝ) (m : ℝ)
    (g FB MB : Fin 3 → ℝ) (t : Time) : Prop :=
  ∂ₜ (bodyVelocity M X) t = m⁻¹ • FB + inertialToBodyVec (M.orientation t) g -
      M.bodyAngularVelocity t ⨯₃ bodyVelocity M X t ∧
    M.inertiaTensorAbout M.centerOfMass *ᵥ ∂ₜ M.bodyAngularVelocity t +
        M.bodyAngularVelocity t ⨯₃
          (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity t) = MB

/-- The package with the reused rotation equation: for constant mass `m > 0`, `C²` position and
orientation on an open set `U` and a body frame centered at the centre of mass, at every `t ∈ U`
the translational law `m X'' = R F_B + m g` and the rotational law `dL_COM/dt = R M_B` both hold
exactly when the six-degree-of-freedom body equations hold. -/
lemma balanceLaws_iff_sixDofBodyEquations (M : RigidBodyMotion 3) (X : Time → Fin 3 → ℝ)
    {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) (hX : ContDiffOn ℝ 2 X U)
    (hc : M.centerOfMass = 0) {m : ℝ} (hm : 0 < m) (g FB MB : Fin 3 → ℝ) {t : Time}
    (ht : t ∈ U) :
    (m • ∂ₜ (∂ₜ X) t = bodyToInertialVec (M.orientation t) FB + m • g ∧
        ∂ₜ (comAngularMomentum M) t = bodyToInertialVec (M.orientation t) MB) ↔
      SixDofBodyEquations M X m g FB MB t := by
  rw [newton_iff_deriv_bodyVelocity M X hU hR hX hm FB g ht,
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

/-- The six-degree-of-freedom plant at time `t` along the state trajectory `x`, the state the maps
read: the state is admitted, and the body equations hold with the force and the moment the maps
give there. -/
def SixDofPlant {S : Type*} (c : ForceMomentMaps S) (x : Time → S) (M : RigidBodyMotion 3)
    (X : Time → Fin 3 → ℝ) (m : ℝ) (g : Fin 3 → ℝ) (t : Time) : Prop :=
  ∃ hx : x t ∈ c.domain,
    SixDofBodyEquations M X m g (c.force ⟨x t, hx⟩) (c.moment ⟨x t, hx⟩) t

/-- The coefficient-map domain wrapper: under the hypotheses of the package, the plant holds at
`t ∈ U` exactly when the state is admitted there and both inertial balance laws hold with the
force and the moment the maps give at that state. -/
lemma sixDofPlant_iff {S : Type*} (c : ForceMomentMaps S) (x : Time → S) (M : RigidBodyMotion 3)
    (X : Time → Fin 3 → ℝ) {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) (hX : ContDiffOn ℝ 2 X U)
    (hc : M.centerOfMass = 0) {m : ℝ} (hm : 0 < m) (g : Fin 3 → ℝ) {t : Time} (ht : t ∈ U) :
    SixDofPlant c x M X m g t ↔ ∃ hx : x t ∈ c.domain,
      m • ∂ₜ (∂ₜ X) t = bodyToInertialVec (M.orientation t) (c.force ⟨x t, hx⟩) + m • g ∧
        ∂ₜ (comAngularMomentum M) t = bodyToInertialVec (M.orientation t) (c.moment ⟨x t, hx⟩) := by
  exact exists_congr fun _ =>
    (balanceLaws_iff_sixDofBodyEquations M X hU hR hX hc hm g _ _ ht).symm

end Mechanics.FlightPlant
