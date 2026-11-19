/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Physlib.ClassicalMechanics.RigidBody.AngularMomentum
public import Physlib.ClassicalMechanics.RigidBody.AngularVelocity
public import PhyslibExt.Units.EngineeringFrames
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Module.FiniteDimension
import MathlibExt.LinearAlgebra.CrossProduct

/-!
# Rotating and translating frames: acceleration and angular momentum

The acceleration of a point in a frame that rotates at a variable rate and translates, derived
from Physlib's rigid-body angular velocity, and the angular momentum of a rigid body in motion
about its centre of mass.

## i. Overview

A frame moves with a rigid body: its orientation is Physlib's `RigidBodyMotion.orientation`
`R(t) ∈ SO(3)` and its origin has inertial coordinates `o(t)`, so a point with body coordinates
`x_B(t)` sits at `x(t) = o(t) + R(t) x_B(t)` (`Units.EngineeringFrames.bodyToInertial`). The
body angular velocity `ω_B` is Physlib's derived `RigidBodyMotion.bodyAngularVelocity`, the
vector dual to `Rᵀ Ṙ`; nothing assumes a transport law.

The product rule and Physlib's `Ṙ v = R (ω_B × v)` give the transport law
`d(R u)/dt = R (u' + ω_B × u)` for a vector with time-dependent body components `u`. Applied
twice it gives `x'' = o'' + R (x_B'' + 2 ω_B × x_B' + ω_B' × x_B + ω_B × (ω_B × x_B))`, with the
relative, Coriolis, Euler and centripetal terms. With constant `ω_B` and a fixed origin this is
the decomposition `a + 2 Ω × v + Ω × (Ω × r)` of
`EarthScience.rotating_acceleration_decomposition`, derived here rather than assumed through a
transport law.

For a rigid body in motion the angular momentum about the centre of mass is
`L_COM(t) = ∫ (x - X(t)) × (v - V(t)) dm` over Physlib's body-fixed mass functional, with `X` the
centre-of-mass trajectory and `V` its velocity. For a body frame centered at the centre of mass,
Physlib's `Ṙ u = R (ω_B × u)`, the invariance of the cross product under rotations and Physlib's
`L = I ω` give `L_COM = R I_B ω_B`, with `I_B` the inertia tensor about the centre of mass in body
axes, and the transport law gives `dL_COM/dt = R (I_B ω_B' + ω_B × (I_B ω_B))`. About a fixed
point `O` the angular momentum gains the orbital term `m (X - O) × V` of the total mass moving
with the centre of mass; about a body point `p`, Physlib's parallel-axis theorem gives
`I_p ω = I_c ω + m (c - p) × (ω × (c - p))`.

Model inputs (hypotheses of the module):

* `R` (entry by entry), `o` and `x_B` are `C²` on an open set of times containing the interval
  considered;
* time derivatives are Physlib's `∂ₜ`; the statements use only Mathlib's default instances on
  matrices (the product topology), so no matrix norm is chosen;
* orientations are proper rotations, as in Physlib's `RigidBodyMotion`; reflections are not
  admissible;
* the mass functional is body-fixed; the total mass is nonzero where the centre of mass enters
  (the shifted reference points); the inertia identity and its derivative take a body frame
  centered at the centre of mass (`centerOfMass = 0`); positivity of the mass or of the inertia
  tensor is not used.

Non-goals: fictitious forces and the equations of motion in the moving frame, torque balance and
Euler's equations, attitude parametrizations, and any empirical adequacy or system safety claim.

## ii. Key results

- `deriv_bodyToInertialVec` : the transport law `d(R u)/dt = R (u' + ω_B × u)`.
- `deriv_deriv_bodyToInertial` : the acceleration in a frame with variable rotation rate and
  translating origin.
- `deriv_deriv_bodyToInertial_of_const` : a constant rate and a fixed origin give the
  constant-rate decomposition.
- `comAngularMomentum_eq` : `L_COM = R I_B ω_B` for a body frame centered at the centre of mass.
- `deriv_comAngularMomentum` : `dL_COM/dt = R (I_B ω_B' + ω_B × (I_B ω_B))`.
- `angularMomentumAbout_eq` : `L_O = L_COM + m (X - O) × V` about a fixed point `O`.
- `inertiaTensorAbout_mulVec_eq_add_orbital` : the parallel-axis theorem for angular momentum.

## iii. Table of contents

- A. Transport of body components
  - A.1. Private calculus helpers
  - A.2. The transport law
- B. Acceleration in a rotating and translating frame
- C. Angular momentum about the centre of mass
- D. Other reference points

## iv. References

- L. D. Landau and E. M. Lifshitz, *Mechanics*, Sections 31, 32 and 39 (angular velocity; the
  angular momentum of a rigid body about its centre of mass and about a fixed point; motion in a
  non-inertial frame of reference, with the translational, Euler, Coriolis and centrifugal
  terms).
- H. Goldstein, C. Poole and J. Safko, *Classical Mechanics*, 3rd edition, 2002, Sections 4.9
  and 4.10 (rate of change of a vector; the Coriolis effect) and Sections 5.1 to 5.3 and 5.5
  (angular momentum and the inertia tensor; the parallel-axis theorem; Euler's equations in body
  axes).
- Physlib's `RigidBodyMotion.bodyAngularVelocity`,
  `RigidBodyMotion.deriv_orientation_mulVec_eq_orientation_bodyAngularVelocity_cross`,
  `RigidBody.angularMomentum_eq_inertiaTensor_mulVec` and
  `RigidBody.inertiaTensorAbout_eq_centerOfMass_add_pointMass`, and the frame dictionary
  `PhyslibExt.Units.EngineeringFrames`.
-/

@[expose] public section

open scoped Matrix
open Time

namespace Mechanics.RigidMotionPorts

open Units.EngineeringFrames

/-! ## A. Transport of body components -/

/-! ### A.1. Private calculus helpers -/

section Helpers

/- The helpers differentiate matrix-valued functions, which needs a norm on matrices. They use the
operator norm of Physlib's angular-velocity file, activated in this section only, so no public
statement depends on it. Mathlib builds that norm with the product topology, so a matrix
differentiability fact stated with the default instances is definitionally the same fact for this
norm. -/
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The matrix-vector product as a continuous bilinear map. -/
private noncomputable def mulVecCLM :
    Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      ((Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) ≃ₗ[ℝ] ((Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))).toLinearMap ∘ₗ
      Matrix.mulVecBilin ℝ ℝ)

/-- The cross product as a continuous bilinear map. -/
private noncomputable def crossCLM : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      ((Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) ≃ₗ[ℝ] ((Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))).toLinearMap ∘ₗ
      crossProduct)

/-- The vee map as a continuous linear map. -/
private noncomputable def veeCLM : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.crossProductVee
      map_add' := fun A B => by ext i; fin_cases i <;> simp [Matrix.crossProductVee]
      map_smul' := fun c A => by ext i; fin_cases i <;> simp [Matrix.crossProductVee] }

/-- Time derivative of a bilinear expression. -/
private lemma deriv_bilin {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) {f : Time → E} {g : Time → F} {t : Time}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    ∂ₜ (fun s => B (f s) (g s)) t = B (f t) (∂ₜ g t) + B (∂ₜ f t) (g t) := by
  rw [Time.deriv_eq, B.fderiv_of_bilinear hf hg]
  rfl

/-- Differentiability of a bilinear expression. -/
private lemma differentiableAt_bilin {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) {f : Time → E} {g : Time → F} {t : Time}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    DifferentiableAt ℝ (fun s => B (f s) (g s)) t :=
  (B.hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt).differentiableAt

/-- The time derivative of a `C²` function on an open set is `C¹` there. -/
private lemma contDiffOn_deriv_of_two {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Time → E} {U : Set Time} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    ContDiffOn ℝ 1 (∂ₜ f) U := by
  have h := hf.fderiv_of_isOpen hU (m := 1) (by norm_num)
  exact h.clm_apply contDiffOn_const

/-- Entrywise `C²` regularity of the orientation gives `C²` regularity for the matrix norm of this
section. -/
private lemma contDiffOn_orientation_of_entries (M : RigidBodyMotion 3) {U : Set Time}
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) :
    ContDiffOn ℝ 2 (fun s => (M.orientation s).1) U := by
  have hpi : ContDiffOn ℝ 2 (fun s => Matrix.of.symm (M.orientation s).1) U :=
    contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => hR i j
  have h := ((Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv :
    (Fin 3 → Fin 3 → ℝ) ≃L[ℝ] Matrix (Fin 3) (Fin 3) ℝ).contDiff.comp_contDiffOn hpi
  convert h using 1
  funext s
  rfl

/-- The body angular velocity is differentiable where the orientation is `C²`. -/
private lemma differentiableAt_bodyAngularVelocity (M : RigidBodyMotion 3) {U : Set Time}
    (hU : IsOpen U) (hR : ContDiffOn ℝ 2 (fun s => (M.orientation s).1) U) {t : Time}
    (ht : t ∈ U) : DifferentiableAt ℝ M.bodyAngularVelocity t := by
  have hR1 : DifferentiableAt ℝ (fun s => (M.orientation s).1) t :=
    (hR.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)
  have hdR : DifferentiableAt ℝ (∂ₜ (fun s => (M.orientation s).1)) t :=
    ((contDiffOn_deriv_of_two hU hR).differentiableOn (by norm_num)).differentiableAt
      (hU.mem_nhds ht)
  have hprod : DifferentiableAt ℝ
      (fun s => ((M.orientation s).1)ᵀ * ∂ₜ (fun s => (M.orientation s).1) s) t :=
    hR1.matrix_transpose.mul hdR
  have : M.bodyAngularVelocity =
      fun s => veeCLM (((M.orientation s).1)ᵀ * ∂ₜ (fun s => (M.orientation s).1) s) := rfl
  rw [this]
  exact veeCLM.differentiableAt.comp t hprod

/-- The transport law with the matrix norm of this section; `deriv_bodyToInertialVec` states it
with the default matrix instances. -/
private lemma deriv_bodyToInertialVec_aux (M : RigidBodyMotion 3) (u : Time → Fin 3 → ℝ) (t : Time)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) (hu : DifferentiableAt ℝ u t) :
    ∂ₜ (fun s => bodyToInertialVec (M.orientation s) (u s)) t =
      bodyToInertialVec (M.orientation t) (∂ₜ u t + M.bodyAngularVelocity t ⨯₃ u t) := by
  have h : ∂ₜ (fun s => (M.orientation s : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u s) t =
      (M.orientation t : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ∂ₜ u t +
        ∂ₜ (fun s => (M.orientation s).1) t *ᵥ u t :=
    deriv_bilin mulVecCLM hR hu
  simp only [bodyToInertialVec]
  rw [h, M.deriv_orientation_mulVec_eq_orientation_bodyAngularVelocity_cross (u t) t hR,
    Matrix.mulVec_add]

/-- Velocity in the moving frame at every time of the open set `U`:
`x' = o' + R (x_B' + ω_B × x_B)`. -/
private lemma deriv_bodyToInertial_of_mem (M : RigidBodyMotion 3) (o xB : Time → Fin 3 → ℝ)
    {U : Set Time} (hU : IsOpen U) (hR : ContDiffOn ℝ 2 (fun s => (M.orientation s).1) U)
    (ho : ContDiffOn ℝ 2 o U) (hx : ContDiffOn ℝ 2 xB U) {τ : Time} (hτ : τ ∈ U) :
    ∂ₜ (fun s => bodyToInertial (o s) (M.orientation s) (xB s)) τ =
      ∂ₜ o τ + bodyToInertialVec (M.orientation τ)
        (∂ₜ xB τ + M.bodyAngularVelocity τ ⨯₃ xB τ) := by
  have hRd : DifferentiableAt ℝ (fun s => (M.orientation s).1) τ :=
    (hR.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hτ)
  have hod : DifferentiableAt ℝ o τ :=
    (ho.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hτ)
  have hxd : DifferentiableAt ℝ xB τ :=
    (hx.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hτ)
  have hv : DifferentiableAt ℝ (fun s => bodyToInertialVec (M.orientation s) (xB s)) τ :=
    differentiableAt_bilin mulVecCLM hRd hxd
  have : (fun s => bodyToInertial (o s) (M.orientation s) (xB s)) =
      fun s => o s + bodyToInertialVec (M.orientation s) (xB s) := rfl
  rw [this, Time.deriv_add _ _ hod hv, deriv_bodyToInertialVec_aux M xB τ hRd hxd]

/-- The acceleration with the matrix norm of this section; `deriv_deriv_bodyToInertial` states it
with the default matrix instances and entrywise regularity of `R`. -/
private lemma deriv_deriv_bodyToInertial_aux (M : RigidBodyMotion 3) (o xB : Time → Fin 3 → ℝ)
    {U : Set Time} (hU : IsOpen U) (hR : ContDiffOn ℝ 2 (fun s => (M.orientation s).1) U)
    (ho : ContDiffOn ℝ 2 o U) (hx : ContDiffOn ℝ 2 xB U) {t : Time} (ht : t ∈ U) :
    ∂ₜ (∂ₜ (fun s => bodyToInertial (o s) (M.orientation s) (xB s))) t =
      ∂ₜ (∂ₜ o) t + bodyToInertialVec (M.orientation t)
        (∂ₜ (∂ₜ xB) t + 2 • (M.bodyAngularVelocity t ⨯₃ ∂ₜ xB t) +
          ∂ₜ M.bodyAngularVelocity t ⨯₃ xB t +
          M.bodyAngularVelocity t ⨯₃ (M.bodyAngularVelocity t ⨯₃ xB t)) := by
  have hUt : U ∈ nhds t := hU.mem_nhds ht
  have hRd : DifferentiableAt ℝ (fun s => (M.orientation s).1) t :=
    (hR.differentiableOn (by norm_num)).differentiableAt hUt
  have hxd : DifferentiableAt ℝ xB t := (hx.differentiableOn (by norm_num)).differentiableAt hUt
  have hdo : DifferentiableAt ℝ (∂ₜ o) t :=
    ((contDiffOn_deriv_of_two hU ho).differentiableOn (by norm_num)).differentiableAt hUt
  have hdx : DifferentiableAt ℝ (∂ₜ xB) t :=
    ((contDiffOn_deriv_of_two hU hx).differentiableOn (by norm_num)).differentiableAt hUt
  have hω : DifferentiableAt ℝ M.bodyAngularVelocity t :=
    differentiableAt_bodyAngularVelocity M hU hR ht
  -- the velocity formula holds on a neighborhood of `t`, so the acceleration is its derivative
  have hev : ∂ₜ (fun s => bodyToInertial (o s) (M.orientation s) (xB s)) =ᶠ[nhds t]
      fun s => ∂ₜ o s + bodyToInertialVec (M.orientation s)
        (∂ₜ xB s + M.bodyAngularVelocity s ⨯₃ xB s) :=
    Filter.eventually_of_mem hUt fun τ hτ => deriv_bodyToInertial_of_mem M o xB hU hR ho hx hτ
  -- differentiate the velocity formula at `t` with the transport law
  have hcr : DifferentiableAt ℝ (fun s => M.bodyAngularVelocity s ⨯₃ xB s) t :=
    differentiableAt_bilin crossCLM hω hxd
  have hvd : DifferentiableAt ℝ (fun s => ∂ₜ xB s + M.bodyAngularVelocity s ⨯₃ xB s) t :=
    hdx.add hcr
  have hw : DifferentiableAt ℝ (fun s => bodyToInertialVec (M.orientation s)
      (∂ₜ xB s + M.bodyAngularVelocity s ⨯₃ xB s)) t :=
    differentiableAt_bilin mulVecCLM hRd hvd
  have hdcr : ∂ₜ (fun s => M.bodyAngularVelocity s ⨯₃ xB s) t =
      M.bodyAngularVelocity t ⨯₃ ∂ₜ xB t + ∂ₜ M.bodyAngularVelocity t ⨯₃ xB t :=
    deriv_bilin crossCLM hω hxd
  rw [Time.deriv_eq, hev.fderiv_eq, ← Time.deriv_eq, Time.deriv_add _ _ hdo hw,
    deriv_bodyToInertialVec_aux M _ t hRd hvd, Time.deriv_add _ _ hdx hcr, hdcr]
  congr 2
  simp only [map_add, two_smul]
  abel

end Helpers

/-! ### A.2. The transport law -/

/-- Transport law: a vector with time-dependent body components `u` has inertial components
`R u`, and `d(R u)/dt = R (u' + ω_B × u)`, with `ω_B` the body angular velocity of the motion. -/
lemma deriv_bodyToInertialVec (M : RigidBodyMotion 3) (u : Time → Fin 3 → ℝ) (t : Time)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) (hu : DifferentiableAt ℝ u t) :
    ∂ₜ (fun s => bodyToInertialVec (M.orientation s) (u s)) t =
      bodyToInertialVec (M.orientation t) (∂ₜ u t + M.bodyAngularVelocity t ⨯₃ u t) := by
  exact deriv_bodyToInertialVec_aux M u t hR hu

/-! ## B. Acceleration in a rotating and translating frame -/

/-- Acceleration of a point in a frame with variable rotation rate and translating origin: for
`x = o + R x_B` with `R` (entry by entry), `o`, `x_B` of class `C²` on the open set `U`, at every
`t ∈ U`, `x'' = o'' + R (x_B'' + 2 ω_B × x_B' + ω_B' × x_B + ω_B × (ω_B × x_B))`. -/
lemma deriv_deriv_bodyToInertial (M : RigidBodyMotion 3) (o xB : Time → Fin 3 → ℝ)
    {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U)
    (ho : ContDiffOn ℝ 2 o U) (hx : ContDiffOn ℝ 2 xB U) {t : Time} (ht : t ∈ U) :
    ∂ₜ (∂ₜ (fun s => bodyToInertial (o s) (M.orientation s) (xB s))) t =
      ∂ₜ (∂ₜ o) t + bodyToInertialVec (M.orientation t)
        (∂ₜ (∂ₜ xB) t + 2 • (M.bodyAngularVelocity t ⨯₃ ∂ₜ xB t) +
          ∂ₜ M.bodyAngularVelocity t ⨯₃ xB t +
          M.bodyAngularVelocity t ⨯₃ (M.bodyAngularVelocity t ⨯₃ xB t)) := by
  exact deriv_deriv_bodyToInertial_aux M o xB hU (contDiffOn_orientation_of_entries M hR) ho hx ht

/-- Constant rate and fixed origin recover the existing constant-rate contract: with
`ω_B = Ω` on `U` and the origin fixed at `o₀`, the acceleration has body components
`a + 2 Ω × v + Ω × (Ω × r)` for `r = x_B`, `v = x_B'`, `a = x_B''`, the right side of
`EarthScience.rotating_acceleration_decomposition`, with no transport law assumed. -/
lemma deriv_deriv_bodyToInertial_of_const (M : RigidBodyMotion 3) (o₀ : Fin 3 → ℝ)
    (xB : Time → Fin 3 → ℝ) (Ω : Fin 3 → ℝ) {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) (hx : ContDiffOn ℝ 2 xB U)
    (hΩ : ∀ s ∈ U, M.bodyAngularVelocity s = Ω) {t : Time} (ht : t ∈ U) :
    ∂ₜ (∂ₜ (fun s => bodyToInertial o₀ (M.orientation s) (xB s))) t =
      bodyToInertialVec (M.orientation t)
        (∂ₜ (∂ₜ xB) t + 2 • (Ω ⨯₃ ∂ₜ xB t) + Ω ⨯₃ (Ω ⨯₃ xB t)) := by
  have h := deriv_deriv_bodyToInertial M (fun _ => o₀) xB hU hR contDiffOn_const hx ht
  have hUt : U ∈ nhds t := hU.mem_nhds ht
  have hωev : M.bodyAngularVelocity =ᶠ[nhds t] fun _ => Ω := Filter.eventually_of_mem hUt hΩ
  have hdω : ∂ₜ M.bodyAngularVelocity t = 0 := by
    rw [Time.deriv_eq, hωev.fderiv_eq]
    simp
  have hdo : ∂ₜ (∂ₜ (fun _ : Time => o₀)) t = 0 := by
    have : ∂ₜ (fun _ : Time => o₀) = fun _ => 0 := by
      funext s
      exact Time.deriv_const o₀
    rw [this]
    exact Time.deriv_const 0
  rw [h, hdo, hdω, hΩ t ht, zero_add]
  simp

open Space (cmap cmap_apply)
open scoped Manifold

/-! ## C. Angular momentum about the centre of mass -/

/-- The angular momentum of a rigid body in motion about its centre of mass,
`L_COM(t) = ∫ (x - X(t)) × (v - V(t)) dm`: for the body point `y`,
`x - X = displacement t y - comTrajectory t` is its position relative to the centre of mass and
`v - V = velocityClosedForm t y - centerOfMassVelocity t` its velocity relative to it (Physlib's
closed-form point velocity, equal to the point velocity for differentiable motions). -/
noncomputable def comAngularMomentum (M : RigidBodyMotion 3) (t : Time) : Fin 3 → ℝ := fun i =>
  M.ρ (cmap (fun y => ((fun j => M.displacement t y j - M.comTrajectory t j) ⨯₃
      (fun j => M.velocityClosedForm t y j - M.centerOfMassVelocity t j)) i)
    (by
      simp only [RigidBodyMotion.displacement_apply, RigidBodyMotion.velocityClosedForm_apply,
        Matrix.mulVec, dotProduct, cross_apply]
      fin_cases i <;>
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, add_sub_cancel_right,
          Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val] <;>
        fun_prop))

/-- The angular momentum of a rigid body in motion about a fixed point `O` of the inertial frame,
`L_O(t) = ∫ (x - O) × v dm`, with `x = displacement t y` and `v = velocityClosedForm t y`. -/
noncomputable def angularMomentumAbout (M : RigidBodyMotion 3) (O : Fin 3 → ℝ) (t : Time) :
    Fin 3 → ℝ := fun i =>
  M.ρ (cmap (fun y => ((fun j => M.displacement t y j - O j) ⨯₃
      (fun j => M.velocityClosedForm t y j)) i)
    (by
      simp only [RigidBodyMotion.displacement_apply, RigidBodyMotion.velocityClosedForm_apply,
        Matrix.mulVec, dotProduct, cross_apply]
      fin_cases i <;>
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta, Fin.mk_one,
          Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
        fun_prop))

/-- The mass-functional identity at a centre-of-mass-centered motion: if the body frame is centered
at the centre of mass (`c = 0`), then `L_COM(t) = R(t) (L_B)` with `L_B` Physlib's angular
momentum of the body-fixed distribution for the body angular velocity, and so
`L_COM(t) = R(t) I_B ω_B(t)` with `I_B` the inertia tensor about the centre of mass. -/
lemma comAngularMomentum_eq (M : RigidBodyMotion 3) (t : Time)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) (hc : M.centerOfMass = 0) :
    comAngularMomentum M t = (M.orientation t).1 *ᵥ M.angularMomentum (M.bodyAngularVelocity t) ∧
      comAngularMomentum M t = (M.orientation t).1 *ᵥ
        (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity t) := by
  have hSO := Matrix.mem_specialOrthogonalGroup_iff.mp (M.orientation t).2
  have hy : ∀ y : Space 3, (fun j => y j - M.centerOfMass j) = (y : Fin 3 → ℝ) := by
    intro y
    funext j
    simp [hc]
  have hint : ∀ y : Space 3, ((fun j => M.displacement t y j - M.comTrajectory t j) ⨯₃
      (fun j => M.velocityClosedForm t y j - M.centerOfMassVelocity t j)) =
      (M.orientation t).1 *ᵥ ((y : Fin 3 → ℝ) ⨯₃ (M.bodyAngularVelocity t ⨯₃ (y : Fin 3 → ℝ))) := by
    intro y
    have hpos : (fun j => M.displacement t y j - M.comTrajectory t j) =
        (M.orientation t).1 *ᵥ (y : Fin 3 → ℝ) := by
      rw [← M.orientation_mulVec_sub_centerOfMass t y, hy]
    have hvel : (fun j => M.velocityClosedForm t y j - M.centerOfMassVelocity t j) =
        (M.orientation t).1 *ᵥ (M.bodyAngularVelocity t ⨯₃ (y : Fin 3 → ℝ)) := by
      funext j
      rw [M.velocityClosedForm_apply, add_sub_cancel_right, hy,
        M.deriv_orientation_mulVec_eq_orientation_bodyAngularVelocity_cross _ t hR]
    rw [hpos, hvel, Matrix.mulVec_cross_mulVec_of_mem_orthogonalGroup hSO.1, hSO.2, one_smul]
  have h1 : comAngularMomentum M t =
      (M.orientation t).1 *ᵥ M.angularMomentum (M.bodyAngularVelocity t) := by
    funext i
    set ω := M.bodyAngularVelocity t with hω
    have hf : ∀ k : Fin 3, ContDiff ℝ ⊤
        (fun x : Space 3 => ((x : Fin 3 → ℝ) ⨯₃ (ω ⨯₃ (x : Fin 3 → ℝ))) k) := by
      intro k
      have h : (fun x : Space 3 => ((x : Fin 3 → ℝ) ⨯₃ (ω ⨯₃ (x : Fin 3 → ℝ))) k)
          = fun x => (∑ l, (x l) ^ 2) * ω k - (∑ j, x j * ω j) * x k :=
        funext fun x => Matrix.cross_cross_self_apply (x : Fin 3 → ℝ) ω k
      rw [h]
      fun_prop
    have hL : ∀ k, M.angularMomentum ω k = M.ρ (Space.cmap _ (hf k)) := fun k => rfl
    simp only [Matrix.mulVec, dotProduct, hL]
    rw [show (∑ k, (M.orientation t).1 i k * M.ρ (Space.cmap _ (hf k))) =
        M.ρ (∑ k, (M.orientation t).1 i k • Space.cmap _ (hf k)) by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]]
    unfold comAngularMomentum
    congr 1
    ext y
    rw [cmap_apply, hint y, ← ContMDiffMap.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
    simp only [ContMDiffMap.coeFnAddMonoidHom_apply, ContMDiffMap.coe_smul, Pi.smul_apply,
      cmap_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  refine ⟨h1, ?_⟩
  rw [h1, RigidBody.angularMomentum_eq_inertiaTensor_mulVec, hc, RigidBody.inertiaTensorAbout_zero]

section DerivativeHelpers

/- The derivative is taken with the operator norm of section A.1, activated here only; the public
statement `deriv_comAngularMomentum` uses the default matrix instances. -/
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The derivative of the centre-of-mass angular momentum with the matrix norm of this section;
`deriv_comAngularMomentum` states it with the default matrix instances and entrywise regularity
of `R`. -/
private lemma deriv_comAngularMomentum_aux (M : RigidBodyMotion 3) {U : Set Time} (hU : IsOpen U)
    (hR : ContDiffOn ℝ 2 (fun s => (M.orientation s).1) U) (hc : M.centerOfMass = 0)
    {t : Time} (ht : t ∈ U) :
    ∂ₜ (comAngularMomentum M) t = (M.orientation t).1 *ᵥ
      (M.inertiaTensorAbout M.centerOfMass *ᵥ ∂ₜ M.bodyAngularVelocity t +
        M.bodyAngularVelocity t ⨯₃
          (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity t)) := by
  have hUt : U ∈ nhds t := hU.mem_nhds ht
  have hRd : ∀ s ∈ U, DifferentiableAt ℝ (fun s => (M.orientation s).1) s := fun s hs =>
    (hR.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hs)
  have hω : DifferentiableAt ℝ M.bodyAngularVelocity t :=
    differentiableAt_bodyAngularVelocity M hU hR ht
  set I := M.inertiaTensorAbout M.centerOfMass with hI
  have hev : comAngularMomentum M =ᶠ[nhds t] fun s =>
      bodyToInertialVec (M.orientation s) (I *ᵥ M.bodyAngularVelocity s) :=
    Filter.eventually_of_mem hUt fun s hs => (comAngularMomentum_eq M s (hRd s hs) hc).2
  have hu : DifferentiableAt ℝ (fun s => I *ᵥ M.bodyAngularVelocity s) t :=
    differentiableAt_bilin mulVecCLM (differentiableAt_const I) hω
  have hdu : ∂ₜ (fun s => I *ᵥ M.bodyAngularVelocity s) t =
      I *ᵥ ∂ₜ M.bodyAngularVelocity t + ∂ₜ (fun _ : Time => I) t *ᵥ M.bodyAngularVelocity t :=
    deriv_bilin mulVecCLM (differentiableAt_const I) hω
  have h0 : ∂ₜ (fun _ : Time => I) t = 0 := by
    rw [Time.deriv_eq]
    simp
  rw [h0, Matrix.zero_mulVec, add_zero] at hdu
  rw [Time.deriv_eq, hev.fderiv_eq, ← Time.deriv_eq, deriv_bodyToInertialVec M _ t (hRd t ht) hu,
    hdu]
  rfl

end DerivativeHelpers

/-- The time derivative along a `C²` motion: with `R` of class `C²` entry by entry on an open set
`U` of times and a centre-of-mass-centered body frame, at every `t ∈ U`,
`dL_COM/dt = R (I_B ω_B' + ω_B × (I_B ω_B))`; `I_B` is constant in the body frame. -/
lemma deriv_comAngularMomentum (M : RigidBodyMotion 3) {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) (hc : M.centerOfMass = 0)
    {t : Time} (ht : t ∈ U) :
    ∂ₜ (comAngularMomentum M) t = (M.orientation t).1 *ᵥ
      (M.inertiaTensorAbout M.centerOfMass *ᵥ ∂ₜ M.bodyAngularVelocity t +
        M.bodyAngularVelocity t ⨯₃
          (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity t)) := by
  exact deriv_comAngularMomentum_aux M hU (contDiffOn_orientation_of_entries M hR) hc ht

/-! ## D. Other reference points -/

/-- Evaluation commutes with finite sums of smooth maps. -/
private lemma contMDiffMap_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → C^⊤⟮𝓘(ℝ, Space 3), Space 3; 𝓘(ℝ, ℝ), ℝ⟯) (y : Space 3) :
    (∑ j ∈ s, f j) y = ∑ j ∈ s, f j y := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp only [Finset.sum_insert ha, ContMDiffMap.coe_add, Pi.add_apply, ih]

/-- A shifted origin needs the translational orbital term: for nonzero mass, the angular momentum
about a fixed point `O` is `L_O = L_COM + m (X - O) × V`. -/
lemma angularMomentumAbout_eq (M : RigidBodyMotion 3) (h : M.mass ≠ 0) (O : Fin 3 → ℝ)
    (t : Time) :
    angularMomentumAbout M O t = comAngularMomentum M t +
      M.mass • ((fun j => M.comTrajectory t j - O j) ⨯₃
        (fun j => M.centerOfMassVelocity t j)) := by
  funext i
  set R := (M.orientation t).1 with hRdef
  set dR := ∂ₜ (fun s => (M.orientation s).1) t with hdR
  set X : Fin 3 → ℝ := fun j => M.comTrajectory t j with hX
  set V : Fin 3 → ℝ := fun j => M.centerOfMassVelocity t j with hV
  set C : Fin 3 → ℝ := fun j =>
    ((fun k => R k j) ⨯₃ V) i + ((fun k => X k - O k) ⨯₃ (fun k => dR k j)) i with hC
  set K : ℝ := ((fun k => X k - O k) ⨯₃ V) i with hK
  have key : ∀ f g : C^⊤⟮𝓘(ℝ, Space 3), Space 3; 𝓘(ℝ, ℝ), ℝ⟯,
      (∀ y, f y = g y + ∑ j, C j * (y j - M.centerOfMass j) + K) →
      M.ρ f = M.ρ g + M.mass * K := by
    intro f g hfg
    have hfun : f = g + (∑ j, C j • Space.cmap (fun y => y j - M.centerOfMass j) (by fun_prop)) +
        K • (1 : C^⊤⟮𝓘(ℝ, Space 3), Space 3; 𝓘(ℝ, ℝ), ℝ⟯) := by
      ext y
      simp only [ContMDiffMap.coe_add, Pi.add_apply, contMDiffMap_sum_apply,
        ContMDiffMap.coe_smul, Pi.smul_apply, cmap_apply, smul_eq_mul, ContMDiffMap.coe_one,
        Pi.one_apply, mul_one]
      exact hfg y
    rw [hfun, map_add, map_add, map_sum]
    simp only [map_smul, M.rho_coord_sub_centerOfMass h, smul_eq_mul, mul_zero,
      Finset.sum_const_zero, add_zero, M.rho_one]
    ring
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply key
  intro y
  simp only [cmap_apply, RigidBodyMotion.displacement_apply,
    RigidBodyMotion.velocityClosedForm_apply, Matrix.mulVec, dotProduct, cross_apply,
    Fin.sum_univ_three, hC, hK, hX, hV, hRdef, hdR]
  fin_cases i <;> simp <;> ring

/-- Physlib's parallel-axis theorem for angular momentum: a body of nonzero mass turning with
angular velocity `ω` about a body point `p` has angular momentum `I_p ω` about `p`, the spin term
`I_c ω` about the centre of mass `c` plus the orbital term `m (c - p) × (ω × (c - p))` of the total
mass at `c`, which moves with velocity `ω × (c - p)`. -/
lemma inertiaTensorAbout_mulVec_eq_add_orbital (B : RigidBody 3) (h : B.mass ≠ 0) (p : Space 3)
    (ω : Fin 3 → ℝ) :
    B.inertiaTensorAbout p *ᵥ ω = B.inertiaTensorAbout B.centerOfMass *ᵥ ω +
      B.mass • ((fun k => B.centerOfMass k - p k) ⨯₃ (ω ⨯₃ fun k => B.centerOfMass k - p k)) := by
  rw [B.inertiaTensorAbout_eq_centerOfMass_add_pointMass h p, Matrix.add_mulVec,
    Matrix.smul_mulVec, Space.inner_eq_sum]
  congr 2
  ext i
  fin_cases i <;>
  · simp [cross_apply, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Space.sub_apply,
      Fin.sum_univ_three, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply]
    ring

end Mechanics.RigidMotionPorts
