/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Physlib.ClassicalMechanics.RigidBody.AngularMomentum
public import Physlib.ClassicalMechanics.RigidBody.AngularVelocity
public import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
public import PhyslibExt.Units.EngineeringFrames
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Module.FiniteDimension
import MathlibExt.LinearAlgebra.CrossProduct

/-!
# Rotating and translating frames: acceleration, angular momentum and Euler's equations

The acceleration of a point in a frame that rotates at a variable rate and translates, derived
from Physlib's rigid-body angular velocity, the angular momentum of a rigid body in motion about
its centre of mass, Euler's equations as the body form of the rotational balance law, a
constructed torque-driven rotation about a fixed principal axis, and the torque-free precession of
the body angular velocity of an axisymmetric body.

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

The rotational balance law `dL_COM/dt = τ_I`, with `τ_I` the external torque about the centre of
mass in inertial components, is a model input. Since `R` is orthogonal, it holds exactly when
Euler's equations `I_B ω_B' + ω_B × (I_B ω_B) = Rᵀ τ_I` hold in body components; for a symmetric
positive-definite `I_B` they determine `ω_B' = I_B⁻¹ (Rᵀ τ_I - ω_B × (I_B ω_B))`. Without torque,
`I_B ω_B'` is orthogonal to `ω_B` and to `I_B ω_B`, so the rotational kinetic energy
`ω_B · (I_B ω_B) / 2` and the squared norm `|I_B ω_B|² = |L_COM|²` of the angular momentum are
conserved.

A body turning about its third body axis, a principal axis through its centre of mass, with the
angle `θ(t) = ω₀ t + α t² / 2` has the explicit orientation `R(t) = Rz(θ(t))`, a `C^∞` curve in
`SO(3)`; differentiating it gives `ω_B = (0, 0, θ')` and `ω_B' = (0, 0, α)`. For a diagonal
inertia `diag(I_xx, I_yy, I_zz)` the gyroscopic term vanishes on the axis, so Euler's equations
need the body torque `τ_B = (0, 0, I_zz α)`, which `Rz` leaves unchanged in inertial components.
This torque port delivers the shaft power `τ_B · ω_B = I_zz α θ'`, the rate of the rotational
kinetic energy. For `I_zz > 0` and `α ≠ 0` the torque is nonzero and the sign-flipped torque
fails. This is existence for this driven example only.

Without torque, an axisymmetric body with principal inertias `I_⊥, I_⊥, I₃` has the body angular
velocity `ω_B(t) = (A cos (ν t), A sin (ν t), ω₃)` with `ν = (I₃ - I_⊥) ω₃ / I_⊥`: the transverse
part turns about the symmetry axis at the rate `ν` while the axial spin stays constant. It solves
Euler's equations `I ω_B' + ω_B × (I ω_B) = 0` with `I = diag(I_⊥, I_⊥, I₃)`; at `t = 0` its
gyroscopic term is `(0, (I_⊥ - I₃) A ω₃, 0)`, nonzero for `I_⊥ ≠ I₃` and `A ω₃ ≠ 0`, and for
positive inertias `euler_solve_iff` recovers its angular acceleration from zero torque. It is a
body angular velocity only: no attitude with this angular velocity is constructed.

Model inputs (hypotheses of the module):

* `R` (entry by entry), `o` and `x_B` are `C²` on an open set of times containing the interval
  considered;
* time derivatives are Physlib's `∂ₜ`; the statements use only Mathlib's default instances on
  matrices (the product topology), so no matrix norm is chosen;
* orientations are proper rotations, as in Physlib's `RigidBodyMotion`; reflections are not
  admissible;
* the mass functional is body-fixed; the total mass is nonzero where the centre of mass enters
  (the shifted reference points); the inertia identity and its derivative take a body frame
  centered at the centre of mass (`centerOfMass = 0`); positivity of the mass is not used, and
  positive definiteness of the inertia tensor is assumed only where Euler's equations are solved
  for `ω_B'`, since an arbitrary linear mass functional does not supply it;
* the rotational balance law `dL_COM/dt = τ_I` is assumed, not derived from internal forces;
  squared magnitudes are dot products, since the norm of `Fin 3 → ℝ` is the supremum norm;
* the constructed rotation takes a mass distribution with diagonal inertia about its centre of
  mass at the origin of body coordinates, and a fixed rotation axis;
* the torque-free precession is stated in principal body axes, with `I_⊥ > 0` (the denominator of
  the rate `ν`) and, where Euler's equations are solved, `I₃ > 0`.

Non-goals: fictitious forces and the equations of motion in the moving frame, existence of motions
for a general torque history (section F constructs one driven example), attitude
parametrizations and reconstruction, and any empirical adequacy or system safety claim.

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
- `deriv_comAngularMomentum_eq_iff_euler` : the balance law `dL_COM/dt = τ_I` holds exactly when
  Euler's equations `I_B ω_B' + ω_B × (I_B ω_B) = Rᵀ τ_I` hold.
- `euler_solve_iff`, `deriv_comAngularMomentum_eq_iff_deriv_bodyAngularVelocity` : a
  positive-definite `I_B` determines the body angular acceleration.
- `torqueFree_conserved` : torque-free motion conserves the rotational kinetic energy and
  `|I_B ω_B|² = |L_COM|²` (`comAngularMomentum_dotProduct_self`).
- `fixedAxisMotion`, `fixedAxisMotion_bodyAngularVelocity`,
  `deriv_fixedAxisMotion_bodyAngularVelocity` : the constructed rotation about a fixed principal
  axis, with `ω_B = (0, 0, θ')` and `ω_B' = (0, 0, α)`.
- `fixedAxisMotion_euler`, `deriv_comAngularMomentum_fixedAxisMotion`,
  `fixedAxisMotion_power_port` : the torque port `τ_B = (0, 0, I_zz α)`, the balance law it
  satisfies and the shaft power it delivers.
- `fixedAxisMotion_torque_ne_zero`, `fixedAxisMotion_neg_torque` : a nonzero angular acceleration
  needs a nonzero torque, and the sign-flipped torque fails.
- `axisymmetricPrecession`, `axisymmetricPrecession_euler` : the torque-free precession of the body
  angular velocity of an axisymmetric body.
- `axisymmetricPrecession_gyroscopic_ne_zero`, `axisymmetricPrecession_euler_solve` : its nonzero
  gyroscopic term, and the Euler port recovering its angular acceleration from zero torque.

## iii. Table of contents

- A. Transport of body components
  - A.1. Private calculus helpers
  - A.2. The transport law
- B. Acceleration in a rotating and translating frame
- C. Angular momentum about the centre of mass
- D. Other reference points
- E. Torque balance and Euler's equations
  - E.1. Private helpers
  - E.2. Euler's equations and torque-free motion
- F. A constructed torque-driven rotation about a fixed principal axis
- G. Torque-free axisymmetric precession

## iv. References

- L. D. Landau and E. M. Lifshitz, *Mechanics*, Sections 31, 32, 34, 36, 37 and 39 (angular
  velocity; the angular momentum of a rigid body about its centre of mass and about a fixed point;
  the equations of motion of a rigid body; Euler's equations, with the free rotation of a
  symmetrical top; the asymmetrical top, whose free rotation conserves the energy and the squared
  angular momentum; motion in a non-inertial frame of reference, with the translational, Euler,
  Coriolis and centrifugal terms).
- H. Goldstein, C. Poole and J. Safko, *Classical Mechanics*, 3rd edition, 2002, Sections 4.9
  and 4.10 (rate of change of a vector; the Coriolis effect) and Sections 5.1 to 5.3, 5.5 and 5.6
  (angular momentum and the inertia tensor; the parallel-axis theorem; Euler's equations in body
  axes; torque-free motion of a rigid body).
- Physlib's `RigidBodyMotion.bodyAngularVelocity`,
  `RigidBodyMotion.deriv_orientation_mulVec_eq_orientation_bodyAngularVelocity_cross`,
  `RigidBody.angularMomentum_eq_inertiaTensor_mulVec`,
  `RigidBody.inertiaTensorAbout_eq_centerOfMass_add_pointMass` and
  `RigidBody.rotationalKineticEnergy`, the frame dictionary
  `PhyslibExt.Units.EngineeringFrames` and the typed shaft power of
  `PhyslibExt.Units.EngineeringQuantities`.
- ISO 80000-4, *Quantities and units — Part 4: Mechanics*: torque and power.
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

/-- Transport law: at a time where `R` and `u` are differentiable, a vector with time-dependent body
components `u` has inertial components `R u`, and `d(R u)/dt = R (u' + ω_B × u)`, with `ω_B` the
body angular velocity of the motion. -/
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

/-- Constant rate and fixed origin recover the existing constant-rate contract: for `R` (entrywise)
and `x_B` of class `C²` on the open set `U`, with `ω_B = Ω` on `U` and the origin fixed at `o₀`,
the acceleration has body components
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

/-! ## E. Torque balance and Euler's equations -/

/-! ### E.1. Private helpers -/

section EulerHelpers

/- The differentiability of `ω_B` comes from the private helpers of section A.1, which use the
operator norm on matrices; it is activated in this section only. -/
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The body angular velocity is differentiable where the orientation is `C²` entry by entry. -/
private lemma differentiableAt_bodyAngularVelocity_of_entries (M : RigidBodyMotion 3)
    {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) {t : Time} (ht : t ∈ U) :
    DifferentiableAt ℝ M.bodyAngularVelocity t :=
  differentiableAt_bodyAngularVelocity M hU (contDiffOn_orientation_of_entries M hR) ht

end EulerHelpers

/-- A time increment is its value times the unit time. -/
private lemma time_eq_val_smul_one (h : Time) : h = h.val • (1 : Time) := by
  ext
  simp [Time.smul_real_val, Time.one_val]

/-- The derivative of `(A f) · (B f)` along a curve `f`, for constant matrices `A` and `B`: its
value on a time increment `h` is `h (A f' · B f + A f · B f')`. -/
private lemma hasFDerivAt_dotProduct_mulVec {f : Time → Fin 3 → ℝ} {t : Time}
    (hf : DifferentiableAt ℝ f t) (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ L : Time →L[ℝ] ℝ, HasFDerivAt (fun s => (A *ᵥ f s) ⬝ᵥ (B *ᵥ f s)) L t ∧
      ∀ h : Time, L h = h.val * ((A *ᵥ ∂ₜ f t) ⬝ᵥ (B *ᵥ f t) + (A *ᵥ f t) ⬝ᵥ (B *ᵥ ∂ₜ f t)) := by
  set f' := fderiv ℝ f t
  let LA : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)
  let LB : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin B)
  have hA : HasFDerivAt (fun s => A *ᵥ f s) (LA.comp f') t := LA.hasFDerivAt.comp t hf.hasFDerivAt
  have hB : HasFDerivAt (fun s => B *ᵥ f s) (LB.comp f') t := LB.hasFDerivAt.comp t hf.hasFDerivAt
  -- differentiate the dot product term by term
  have hcomp : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      HasFDerivAt (fun s => (A *ᵥ f s) i * (B *ᵥ f s) i)
        ((A *ᵥ f t) i • ((ContinuousLinearMap.proj i).comp (LB.comp f')) +
          (B *ᵥ f t) i • ((ContinuousLinearMap.proj i).comp (LA.comp f'))) t := by
    intro i _
    have hAi : HasFDerivAt (fun s => (A *ᵥ f s) i)
        ((ContinuousLinearMap.proj i).comp (LA.comp f')) t :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp t hA
    have hBi : HasFDerivAt (fun s => (B *ᵥ f s) i)
        ((ContinuousLinearMap.proj i).comp (LB.comp f')) t :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp t hB
    exact hAi.mul hBi
  refine ⟨∑ i, ((A *ᵥ f t) i • (ContinuousLinearMap.proj i).comp (LB.comp f') +
    (B *ᵥ f t) i • (ContinuousLinearMap.proj i).comp (LA.comp f')), ?_, fun h => ?_⟩
  · convert HasFDerivAt.sum hcomp using 1
    funext s
    simp [dotProduct, Finset.sum_apply]
  · -- on the increment `h`, the derivative of `f` is `h.val • ∂ₜ f t`
    have h1 : f' h = h.val • ∂ₜ f t := by
      conv_lhs => rw [time_eq_val_smul_one h]
      rw [map_smul]
      rfl
    simp only [sum_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, h1]
    simp only [LA, LB, LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply,
      Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-! ### E.2. Euler's equations and torque-free motion -/

/-- Transport of the declared balance law: along a motion whose orientation is `C²` entry by entry
on an open set `U` of times, with a centre-of-mass-centered body frame, at every `t ∈ U` the
inertial law `dL_COM/dt = τ_I` holds exactly when Euler's equations
`I_B ω_B' + ω_B × (I_B ω_B) = Rᵀ τ_I` hold in body components. -/
lemma deriv_comAngularMomentum_eq_iff_euler (M : RigidBodyMotion 3) {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) (hc : M.centerOfMass = 0)
    {t : Time} (ht : t ∈ U) (τI : Fin 3 → ℝ) :
    ∂ₜ (comAngularMomentum M) t = τI ↔
      M.inertiaTensorAbout M.centerOfMass *ᵥ ∂ₜ M.bodyAngularVelocity t +
          M.bodyAngularVelocity t ⨯₃
            (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity t) =
        inertialToBodyVec (M.orientation t) τI := by
  rw [deriv_comAngularMomentum M hU hR hc ht]
  constructor
  · intro h
    rw [← h]
    exact (inertialToBodyVec_bodyToInertialVec (M.orientation t) _).symm
  · intro h
    change bodyToInertialVec (M.orientation t) _ = τI
    rw [h]
    exact bodyToInertialVec_inertialToBodyVec (M.orientation t) τI

/-- For a symmetric positive-definite inertia `I`, Euler's equations `I a + ω × (I ω) = τ_B` in the
angular acceleration `a` have the unique solution `a = I⁻¹ (τ_B - ω × (I ω))`. -/
lemma euler_solve_iff {I : Matrix (Fin 3) (Fin 3) ℝ} (hI : I.PosDef) (ω a τB : Fin 3 → ℝ) :
    I *ᵥ a + ω ⨯₃ (I *ᵥ ω) = τB ↔ a = I⁻¹ *ᵥ (τB - ω ⨯₃ (I *ᵥ ω)) := by
  have hdet : IsUnit I.det := (Matrix.isUnit_iff_isUnit_det I).mp hI.isUnit
  constructor
  · intro h
    rw [← h, add_sub_cancel_right, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul I hdet,
      Matrix.one_mulVec]
  · intro h
    rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv I hdet, Matrix.one_mulVec, sub_add_cancel]

/-- For `c = 0`, `R` of class `C²` entrywise on the open set `U` and a positive-definite inertia
tensor about the centre of mass, the balance law determines the body angular acceleration: at
every `t ∈ U`, `dL_COM/dt = τ_I` exactly when
`ω_B' = I_B⁻¹ (Rᵀ τ_I - ω_B × (I_B ω_B))`. -/
lemma deriv_comAngularMomentum_eq_iff_deriv_bodyAngularVelocity (M : RigidBodyMotion 3)
    {U : Set Time} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U) (hc : M.centerOfMass = 0)
    (hI : (M.inertiaTensorAbout M.centerOfMass).PosDef) {t : Time} (ht : t ∈ U)
    (τI : Fin 3 → ℝ) :
    ∂ₜ (comAngularMomentum M) t = τI ↔
      ∂ₜ M.bodyAngularVelocity t = (M.inertiaTensorAbout M.centerOfMass)⁻¹ *ᵥ
        (inertialToBodyVec (M.orientation t) τI -
          M.bodyAngularVelocity t ⨯₃
            (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity t)) := by
  rw [deriv_comAngularMomentum_eq_iff_euler M hU hR hc ht τI]
  exact euler_solve_iff hI _ _ _

/-- The body and inertial angular momenta have the same Euclidean norm:
`L_COM · L_COM = (I_B ω_B) · (I_B ω_B)` for a centre-of-mass-centered body frame. -/
lemma comAngularMomentum_dotProduct_self (M : RigidBodyMotion 3) (t : Time)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) (hc : M.centerOfMass = 0) :
    comAngularMomentum M t ⬝ᵥ comAngularMomentum M t =
      (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity t) ⬝ᵥ
        (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity t) := by
  rw [(comAngularMomentum_eq M t hR hc).2]
  exact bodyToInertialVec_dotProduct (M.orientation t) _ _

/-- Torque-free consequence for the kinetic energy: for `c = 0` and `R` of class `C²` entrywise on
the open set `U`, if `dL_COM/dt = 0` at `t ∈ U`, the rotational
kinetic energy `ω_B · (I_B ω_B) / 2` (Physlib's `rotationalKineticEnergy` of the body-fixed
distribution, the rotational part of the total kinetic energy) has derivative zero at `t`. -/
lemma hasFDerivAt_rotationalKineticEnergy_of_torqueFree (M : RigidBodyMotion 3) {U : Set Time}
    (hU : IsOpen U) (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U)
    (hc : M.centerOfMass = 0) {t : Time} (ht : t ∈ U)
    (hfree : ∂ₜ (comAngularMomentum M) t = 0) :
    HasFDerivAt (fun s => M.toRigidBody.rotationalKineticEnergy (M.bodyAngularVelocity s))
      (0 : Time →L[ℝ] ℝ) t := by
  have hω := differentiableAt_bodyAngularVelocity_of_entries M hU hR ht
  -- without torque, Euler's equations read `I_B ω_B' = -(ω_B × (I_B ω_B))`
  have heul := (deriv_comAngularMomentum_eq_iff_euler M hU hR hc ht 0).mp hfree
  simp only [inertialToBodyVec, Matrix.mulVec_zero] at heul
  have hI : M.toRigidBody.inertiaTensor = M.inertiaTensorAbout M.centerOfMass := by
    rw [hc, RigidBody.inertiaTensorAbout_zero]
  set I := M.inertiaTensorAbout M.centerOfMass
  have hsymm : Iᵀ = I := by
    ext i j
    exact RigidBody.inertiaTensorAbout_symmetric _ _ j i
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_dotProduct_mulVec hω 1 I
  have hfun : (fun s => M.toRigidBody.rotationalKineticEnergy (M.bodyAngularVelocity s)) =
      fun s => (1 / (2 : ℝ)) * ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ M.bodyAngularVelocity s) ⬝ᵥ
        (I *ᵥ M.bodyAngularVelocity s) := by
    funext s
    simp [RigidBody.rotationalKineticEnergy, hI]
  rw [hfun]
  -- by the symmetry of `I_B`, the derivative is `ω_B · (I_B ω_B') = -ω_B · (ω_B × (I_B ω_B)) = 0`
  have hL0 : (1 / (2 : ℝ)) • L = 0 := by
    refine ContinuousLinearMap.ext fun h => ?_
    rw [smul_apply, hLv h, zero_apply]
    simp only [Matrix.one_mulVec]
    set ω := M.bodyAngularVelocity t
    set a := ∂ₜ M.bodyAngularVelocity t
    have e1 : a ⬝ᵥ (I *ᵥ ω) = ω ⬝ᵥ (I *ᵥ a) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]
    have e2 : I *ᵥ a = -(ω ⨯₃ (I *ᵥ ω)) := eq_neg_of_add_eq_zero_left heul
    rw [e1, e2, dotProduct_neg, dot_self_cross]
    simp
  have h := hL.const_mul (1 / (2 : ℝ))
  rw [hL0] at h
  exact h

/-- Torque-free consequence for the angular momentum: for `c = 0` and `R` of class `C²` entrywise
on the open set `U`, if `dL_COM/dt = 0` at `t ∈ U`, the squared
Euclidean norm `(I_B ω_B) · (I_B ω_B)` of the body angular momentum has derivative zero at `t`. -/
lemma hasFDerivAt_angularMomentum_normSq_of_torqueFree (M : RigidBodyMotion 3) {U : Set Time}
    (hU : IsOpen U) (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U)
    (hc : M.centerOfMass = 0) {t : Time} (ht : t ∈ U)
    (hfree : ∂ₜ (comAngularMomentum M) t = 0) :
    HasFDerivAt (fun s => (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity s) ⬝ᵥ
        (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity s))
      (0 : Time →L[ℝ] ℝ) t := by
  have hω := differentiableAt_bodyAngularVelocity_of_entries M hU hR ht
  -- without torque, Euler's equations read `I_B ω_B' = -(ω_B × (I_B ω_B))`
  have heul := (deriv_comAngularMomentum_eq_iff_euler M hU hR hc ht 0).mp hfree
  simp only [inertialToBodyVec, Matrix.mulVec_zero] at heul
  set I := M.inertiaTensorAbout M.centerOfMass
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_dotProduct_mulVec hω I I
  -- the derivative is `2 (I_B ω_B) · (I_B ω_B') = -2 (I_B ω_B) · (ω_B × (I_B ω_B)) = 0`
  have hL0 : L = 0 := by
    refine ContinuousLinearMap.ext fun h => ?_
    rw [hLv h, zero_apply]
    set ω := M.bodyAngularVelocity t
    set a := ∂ₜ M.bodyAngularVelocity t
    have e2 : I *ᵥ a = -(ω ⨯₃ (I *ᵥ ω)) := eq_neg_of_add_eq_zero_left heul
    have z1 : (I *ᵥ ω) ⬝ᵥ (ω ⨯₃ (I *ᵥ ω)) = 0 := dot_cross_self _ _
    have z2 : (ω ⨯₃ (I *ᵥ ω)) ⬝ᵥ (I *ᵥ ω) = 0 := by
      rw [dotProduct_comm]
      exact z1
    rw [e2]
    simp only [neg_dotProduct, dotProduct_neg, z1, z2, neg_zero, add_zero, mul_zero]
  rw [hL0] at hL
  exact hL

/-- Conservation on a preconnected open set `U` of times on which `R` is `C²` entrywise, for
`c = 0`: if `dL_COM/dt = 0` on `U`, the rotational kinetic energy and the squared norm
`|I_B ω_B|² = |L_COM|²` of the angular momentum are constant on `U`. -/
lemma torqueFree_conserved (M : RigidBodyMotion 3) {U : Set Time} (hU : IsOpen U)
    (hU' : IsPreconnected U) (hR : ∀ i j, ContDiffOn ℝ 2 (fun s => (M.orientation s).1 i j) U)
    (hc : M.centerOfMass = 0) (hfree : ∀ s ∈ U, ∂ₜ (comAngularMomentum M) s = 0) {s t : Time}
    (hs : s ∈ U) (ht : t ∈ U) :
    M.toRigidBody.rotationalKineticEnergy (M.bodyAngularVelocity s) =
        M.toRigidBody.rotationalKineticEnergy (M.bodyAngularVelocity t) ∧
      (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity s) ⬝ᵥ
          (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity s) =
        (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity t) ⬝ᵥ
          (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity t) := by
  have hE : ∀ τ ∈ U, HasFDerivAt
      (fun s => M.toRigidBody.rotationalKineticEnergy (M.bodyAngularVelocity s))
      (0 : Time →L[ℝ] ℝ) τ := fun τ hτ =>
    hasFDerivAt_rotationalKineticEnergy_of_torqueFree M hU hR hc hτ (hfree τ hτ)
  have hN : ∀ τ ∈ U, HasFDerivAt
      (fun s => (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity s) ⬝ᵥ
        (M.inertiaTensorAbout M.centerOfMass *ᵥ M.bodyAngularVelocity s))
      (0 : Time →L[ℝ] ℝ) τ := fun τ hτ =>
    hasFDerivAt_angularMomentum_normSq_of_torqueFree M hU hR hc hτ (hfree τ hτ)
  refine ⟨?_, ?_⟩
  · exact hU.is_const_of_fderiv_eq_zero (𝕜 := ℝ) hU'
      (fun τ hτ => (hE τ hτ).differentiableAt.differentiableWithinAt)
      (fun τ hτ => (hE τ hτ).fderiv) hs ht
  · exact hU.is_const_of_fderiv_eq_zero (𝕜 := ℝ) hU'
      (fun τ hτ => (hN τ hτ).differentiableAt.differentiableWithinAt)
      (fun τ hτ => (hN τ hτ).fderiv) hs ht

/-! ## F. A constructed torque-driven rotation about a fixed principal axis -/

open scoped ContDiff
open Units.EngineeringQuantities

/-- The rotation angle `θ(t) = ω₀ t + α t² / 2` about the third axis: initial rate `ω₀` and
constant angular acceleration `α`. -/
noncomputable def fixedAxisAngle (ω₀ α : ℝ) (t : Time) : ℝ := ω₀ * t.val + α * t.val ^ 2 / 2

/-- The constructed motion of the mass distribution `B` about its third body axis: the centre of
mass rests at the origin and the orientation is `R(t) = Rz(θ(t))`, a curve in `SO(3)`. -/
noncomputable def fixedAxisMotion (B : RigidBody 3) (ω₀ α : ℝ) : RigidBodyMotion 3 where
  toRigidBody := B
  comTrajectory := fun _ => 0
  orientation := fun t => ⟨rotZ (fixedAxisAngle ω₀ α t), rotZ_mem_specialOrthogonalGroup _⟩

/-- The torque port of the fixed-axis motion: the body torque `τ_B = (0, 0, I_zz α)` about the
centre of mass, which, for a body with inertia `diag(I_xx, I_yy, I_zz)` about its centre of mass,
drives the constant angular acceleration `α`. -/
noncomputable def fixedAxisTorque (Izz α : ℝ) : Fin 3 → ℝ := ![0, 0, Izz * α]

/-- The angle `θ(t) = ω₀ t + α t² / 2` as a curve on `ℝ` has the rate `ω₀ + α t`. -/
private lemma hasDerivAt_fixedAxisAngle (ω₀ α x : ℝ) :
    HasDerivAt (fun y : ℝ => fixedAxisAngle ω₀ α ⟨y⟩) (ω₀ + α * x) x := by
  have h := ((hasDerivAt_id x).const_mul ω₀).add (((hasDerivAt_pow 2 x).const_mul α).div_const 2)
  convert h using 1
  · funext y
    simp [fixedAxisAngle]
  · push_cast
    ring

/-- The constructed orientation is `C^∞` entry by entry. -/
lemma contDiff_fixedAxisMotion_orientation_apply (B : RigidBody 3) (ω₀ α : ℝ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun s => ((fixedAxisMotion B ω₀ α).orientation s).1 i j) := by
  have hθ : ContDiff ℝ ∞ (fixedAxisAngle ω₀ α) := by
    unfold fixedAxisAngle
    fun_prop
  have hc := Real.contDiff_cos.comp hθ
  have hs := Real.contDiff_sin.comp hθ
  fin_cases i <;> fin_cases j <;> simp only [fixedAxisMotion, rotZ] <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;>
    first
      | exact hc
      | exact hs
      | exact hs.neg
      | exact contDiff_const

/-- The constructed orientation is differentiable with the default matrix instances. -/
private lemma differentiableAt_fixedAxisMotion_orientation (B : RigidBody 3) (ω₀ α : ℝ)
    (t : Time) : DifferentiableAt ℝ (fun s => ((fixedAxisMotion B ω₀ α).orientation s).1) t := by
  have h : DifferentiableAt ℝ
      (fun s => Matrix.of.symm ((fixedAxisMotion B ω₀ α).orientation s).1) t :=
    differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j =>
      ((contDiff_fixedAxisMotion_orientation_apply B ω₀ α i j).differentiable (by simp)) t
  exact h

/-- The angle has the rate `θ'(t) = ω₀ + α t` and the constant second derivative `θ'' = α`. -/
lemma deriv_fixedAxisAngle (ω₀ α : ℝ) (t : Time) :
    ∂ₜ (fixedAxisAngle ω₀ α) t = ω₀ + α * t.val ∧ ∂ₜ (∂ₜ (fixedAxisAngle ω₀ α)) t = α := by
  have h1 : ∀ s : Time, ∂ₜ (fixedAxisAngle ω₀ α) s = ω₀ + α * s.val := fun s =>
    Time.deriv_eq_of_hasDerivAt (hasDerivAt_fixedAxisAngle ω₀ α s.val)
  refine ⟨h1 t, ?_⟩
  have hfun : ∂ₜ (fixedAxisAngle ω₀ α) = fun s => ω₀ + α * s.val := funext h1
  rw [hfun]
  apply Time.deriv_eq_of_hasDerivAt
  simpa using ((hasDerivAt_id t.val).const_mul α).const_add ω₀

/-- The orientation has the derivative `Ṙ = θ' dRz/dθ`, with
`dRz/dθ = [[-sin θ, -cos θ, 0], [cos θ, -sin θ, 0], [0, 0, 0]]`. -/
lemma deriv_fixedAxisMotion_orientation (B : RigidBody 3) (ω₀ α : ℝ) (t : Time) :
    ∂ₜ (fun s => ((fixedAxisMotion B ω₀ α).orientation s).1) t =
      ∂ₜ (fixedAxisAngle ω₀ α) t •
        !![-Real.sin (fixedAxisAngle ω₀ α t), -Real.cos (fixedAxisAngle ω₀ α t), 0;
          Real.cos (fixedAxisAngle ω₀ α t), -Real.sin (fixedAxisAngle ω₀ α t), 0; 0, 0, 0] := by
  have hθ := hasDerivAt_fixedAxisAngle ω₀ α t.val
  have hθ' := (deriv_fixedAxisAngle ω₀ α t).1
  have dc : ∂ₜ (fun s : Time => Real.cos (fixedAxisAngle ω₀ α s)) t =
      ∂ₜ (fixedAxisAngle ω₀ α) t * -Real.sin (fixedAxisAngle ω₀ α t) := by
    rw [hθ']
    exact Time.deriv_eq_of_hasDerivAt
      (((Real.hasDerivAt_cos _).comp t.val hθ).congr_deriv (by ring))
  have ds : ∂ₜ (fun s : Time => Real.sin (fixedAxisAngle ω₀ α s)) t =
      ∂ₜ (fixedAxisAngle ω₀ α) t * Real.cos (fixedAxisAngle ω₀ α t) := by
    rw [hθ']
    exact Time.deriv_eq_of_hasDerivAt
      (((Real.hasDerivAt_sin _).comp t.val hθ).congr_deriv (by ring))
  have dns : ∂ₜ (fun s : Time => -Real.sin (fixedAxisAngle ω₀ α s)) t =
      ∂ₜ (fixedAxisAngle ω₀ α) t * -Real.cos (fixedAxisAngle ω₀ α t) := by
    rw [hθ']
    exact Time.deriv_eq_of_hasDerivAt
      (((Real.hasDerivAt_sin _).comp t.val hθ).neg.congr_deriv (by ring))
  ext i j
  refine (Time.deriv_matrix_apply _ t
    (differentiableAt_fixedAxisMotion_orientation B ω₀ α t) i j).symm.trans ?_
  fin_cases i <;> fin_cases j <;> simp only [fixedAxisMotion, rotZ] <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.smul_apply, smul_eq_mul] <;>
    first
      | exact dc
      | exact ds
      | exact dns
      | simp

/-- The body angular velocity of the constructed motion is `ω_B = (0, 0, θ')`. -/
lemma fixedAxisMotion_bodyAngularVelocity (B : RigidBody 3) (ω₀ α : ℝ) (t : Time) :
    (fixedAxisMotion B ω₀ α).bodyAngularVelocity t = ![0, 0, ∂ₜ (fixedAxisAngle ω₀ α) t] := by
  have h : (fixedAxisMotion B ω₀ α).bodyAngularVelocity t = Matrix.crossProductVee
      ((((fixedAxisMotion B ω₀ α).orientation t : Matrix (Fin 3) (Fin 3) ℝ))ᵀ *
        ∂ₜ (fun s => ((fixedAxisMotion B ω₀ α).orientation s).1) t) := rfl
  rw [h, deriv_fixedAxisMotion_orientation]
  have hR : (((fixedAxisMotion B ω₀ α).orientation t : Matrix (Fin 3) (Fin 3) ℝ)) =
      rotZ (fixedAxisAngle ω₀ α t) := rfl
  rw [hR]
  have hcs := Real.cos_sq_add_sin_sq (fixedAxisAngle ω₀ α t)
  ext i
  fin_cases i
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.crossProductVee, rotZ, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ∂ₜ (fixedAxisAngle ω₀ α) t * hcs

/-- The body angular acceleration of the constructed motion is `ω_B' = (0, 0, α)`. -/
lemma deriv_fixedAxisMotion_bodyAngularVelocity (B : RigidBody 3) (ω₀ α : ℝ) (t : Time) :
    ∂ₜ (fixedAxisMotion B ω₀ α).bodyAngularVelocity t = ![0, 0, α] := by
  have hω : (fixedAxisMotion B ω₀ α).bodyAngularVelocity =
      fun s => (fun x : ℝ => ![0, 0, ω₀ + α * x]) (Time.toRealCLE s) := by
    funext s
    rw [fixedAxisMotion_bodyAngularVelocity, (deriv_fixedAxisAngle ω₀ α s).1]
    rfl
  have hγ : HasDerivAt (fun x : ℝ => ![0, 0, ω₀ + α * x]) ![0, 0, α] (Time.toRealCLE t) := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hasDerivAt_const (Time.toRealCLE t) (0 : ℝ)
    · simpa using hasDerivAt_const (Time.toRealCLE t) (0 : ℝ)
    · simpa using ((hasDerivAt_id (Time.toRealCLE t)).const_mul α).const_add ω₀
  rw [hω]
  exact Time.deriv_comp_toRealCLE_of_hasDerivAt _ t _ hγ

/-- Euler's equations of the torque-balance section on the constructed motion: for a diagonal
inertia `diag(I_xx, I_yy, I_zz)` about the centre of mass the gyroscopic term vanishes on the axis,
and `I_B ω_B' + ω_B × (I_B ω_B) = (0, 0, I_zz α)`, the port torque. -/
lemma fixedAxisMotion_euler {B : RigidBody 3} {Ixx Iyy Izz : ℝ}
    (hI : B.inertiaTensorAbout B.centerOfMass = Matrix.diagonal ![Ixx, Iyy, Izz]) (ω₀ α : ℝ)
    (t : Time) :
    (fixedAxisMotion B ω₀ α).inertiaTensorAbout (fixedAxisMotion B ω₀ α).centerOfMass *ᵥ
          ∂ₜ (fixedAxisMotion B ω₀ α).bodyAngularVelocity t +
        (fixedAxisMotion B ω₀ α).bodyAngularVelocity t ⨯₃
          ((fixedAxisMotion B ω₀ α).inertiaTensorAbout (fixedAxisMotion B ω₀ α).centerOfMass *ᵥ
            (fixedAxisMotion B ω₀ α).bodyAngularVelocity t) =
      fixedAxisTorque Izz α := by
  have hI' : (fixedAxisMotion B ω₀ α).inertiaTensorAbout (fixedAxisMotion B ω₀ α).centerOfMass =
      Matrix.diagonal ![Ixx, Iyy, Izz] := hI
  rw [hI', fixedAxisMotion_bodyAngularVelocity, deriv_fixedAxisMotion_bodyAngularVelocity]
  ext i
  fin_cases i <;> simp [Matrix.mulVec_diagonal, cross_apply, fixedAxisTorque]

/-- The balance law of the torque-balance section holds on the constructed motion with the port
torque: for a mass distribution with centre of mass `0` and diagonal inertia,
`dL_COM/dt = R τ_B`, and `R τ_B = τ_B = (0, 0, I_zz α)` since `Rz` fixes the third axis. -/
lemma deriv_comAngularMomentum_fixedAxisMotion {B : RigidBody 3} (hc : B.centerOfMass = 0)
    {Ixx Iyy Izz : ℝ} (hI : B.inertiaTensorAbout B.centerOfMass = Matrix.diagonal ![Ixx, Iyy, Izz])
    (ω₀ α : ℝ) (t : Time) :
    ∂ₜ (comAngularMomentum (fixedAxisMotion B ω₀ α)) t =
        bodyToInertialVec ((fixedAxisMotion B ω₀ α).orientation t) (fixedAxisTorque Izz α) ∧
      bodyToInertialVec ((fixedAxisMotion B ω₀ α).orientation t) (fixedAxisTorque Izz α) =
        fixedAxisTorque Izz α := by
  have hR : ∀ i j, ContDiffOn ℝ 2 (fun s => ((fixedAxisMotion B ω₀ α).orientation s).1 i j)
      Set.univ := fun i j =>
    (contDiff_infty.1 (contDiff_fixedAxisMotion_orientation_apply B ω₀ α i j) 2).contDiffOn
  have hc' : (fixedAxisMotion B ω₀ α).centerOfMass = 0 := hc
  refine ⟨?_, ?_⟩
  · refine (deriv_comAngularMomentum_eq_iff_euler (fixedAxisMotion B ω₀ α) isOpen_univ hR hc'
      (Set.mem_univ t) _).mpr ?_
    rw [inertialToBodyVec_bodyToInertialVec]
    exact fixedAxisMotion_euler hI ω₀ α t
  · have hR' : (((fixedAxisMotion B ω₀ α).orientation t : Matrix (Fin 3) (Fin 3) ℝ)) =
        rotZ (fixedAxisAngle ω₀ α t) := rfl
    simp only [bodyToInertialVec, hR']
    ext i
    fin_cases i <;> simp [rotZ, Matrix.mulVec, dotProduct, Fin.sum_univ_three, fixedAxisTorque]

/-- The torque port delivers the shaft power `P = τ ω` about the axis: for `c = 0` and inertia
`diag(I_xx, I_yy, I_zz)` about it, the rotational kinetic energy
`T = ω_B · (I_B ω_B) / 2 = I_zz θ'² / 2` is differentiable with rate
`τ_B · ω_B = I_zz α θ'`, the coordinate of the typed shaft power of the torque `I_zz α` at the
angular velocity `θ'`. -/
lemma fixedAxisMotion_power_port {B : RigidBody 3} (hc : B.centerOfMass = 0) {Ixx Iyy Izz : ℝ}
    (hI : B.inertiaTensorAbout B.centerOfMass = Matrix.diagonal ![Ixx, Iyy, Izz]) (ω₀ α : ℝ)
    (t : Time) :
    DifferentiableAt ℝ
        (fun s => B.rotationalKineticEnergy ((fixedAxisMotion B ω₀ α).bodyAngularVelocity s)) t ∧
      ∂ₜ (fun s => B.rotationalKineticEnergy ((fixedAxisMotion B ω₀ α).bodyAngularVelocity s)) t =
        fixedAxisTorque Izz α ⬝ᵥ (fixedAxisMotion B ω₀ α).bodyAngularVelocity t ∧
      fixedAxisTorque Izz α ⬝ᵥ (fixedAxisMotion B ω₀ α).bodyAngularVelocity t =
        (shaftPower ⟨Izz * α⟩ ⟨∂ₜ (fixedAxisAngle ω₀ α) t⟩).val := by
  have hT : B.inertiaTensor = Matrix.diagonal ![Ixx, Iyy, Izz] := by
    rw [← RigidBody.inertiaTensorAbout_zero, ← hc, hI]
  have hfun : (fun s => B.rotationalKineticEnergy ((fixedAxisMotion B ω₀ α).bodyAngularVelocity s))
      = fun s => (fun x : ℝ => Izz * (ω₀ + α * x) ^ 2 / 2) (Time.toRealCLE s) := by
    funext s
    rw [RigidBody.rotationalKineticEnergy, hT, fixedAxisMotion_bodyAngularVelocity,
      (deriv_fixedAxisAngle ω₀ α s).1]
    have hv : Matrix.diagonal ![Ixx, Iyy, Izz] *ᵥ ![0, 0, ω₀ + α * s.val] =
        ![0, 0, Izz * (ω₀ + α * s.val)] := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec_diagonal]
    rw [hv]
    simp only [Matrix.cons_dotProduct, Matrix.head_cons, Matrix.tail_cons,
      Matrix.dotProduct_of_isEmpty, zero_mul, zero_add, add_zero]
    change _ = Izz * (ω₀ + α * s.val) ^ 2 / 2
    ring
  have hγ : HasDerivAt (fun x : ℝ => Izz * (ω₀ + α * x) ^ 2 / 2)
      (Izz * α * (ω₀ + α * Time.toRealCLE t)) (Time.toRealCLE t) := by
    have hl : HasDerivAt (fun x : ℝ => ω₀ + α * x) α (Time.toRealCLE t) := by
      simpa using ((hasDerivAt_id (Time.toRealCLE t)).const_mul α).const_add ω₀
    have h := ((hl.pow 2).const_mul Izz).div_const 2
    convert h using 1
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have hP : fixedAxisTorque Izz α ⬝ᵥ (fixedAxisMotion B ω₀ α).bodyAngularVelocity t =
      Izz * α * (ω₀ + α * t.val) := by
    rw [fixedAxisMotion_bodyAngularVelocity, (deriv_fixedAxisAngle ω₀ α t).1]
    simp [fixedAxisTorque, dotProduct, Fin.sum_univ_three]
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact hγ.differentiableAt.comp t Time.toRealCLE.differentiableAt
  · rw [hfun, hP]
    exact Time.deriv_comp_toRealCLE_of_hasDerivAt _ t _ hγ
  · rw [shaftPower_val, hP, (deriv_fixedAxisAngle ω₀ α t).1]

/-- A nonzero angular acceleration needs a nonzero torque: for `c = 0`, inertia
`diag(I_xx, I_yy, I_zz)` about it, `I_zz > 0` and `α ≠ 0` the port torque, the body angular
acceleration and the rate of change `dL_COM/dt` are nonzero. -/
lemma fixedAxisMotion_torque_ne_zero {B : RigidBody 3} (hc : B.centerOfMass = 0)
    {Ixx Iyy Izz : ℝ} (hI : B.inertiaTensorAbout B.centerOfMass = Matrix.diagonal ![Ixx, Iyy, Izz])
    (hIzz : 0 < Izz) {ω₀ α : ℝ} (hα : α ≠ 0) (t : Time) :
    fixedAxisTorque Izz α ≠ 0 ∧ ∂ₜ (fixedAxisMotion B ω₀ α).bodyAngularVelocity t ≠ 0 ∧
      ∂ₜ (comAngularMomentum (fixedAxisMotion B ω₀ α)) t ≠ 0 := by
  have hτ : fixedAxisTorque Izz α ≠ 0 := by
    intro h
    exact mul_ne_zero hIzz.ne' hα (by simpa [fixedAxisTorque] using congrFun h 2)
  refine ⟨hτ, ?_, ?_⟩
  · rw [deriv_fixedAxisMotion_bodyAngularVelocity]
    intro h
    exact hα (by simpa using congrFun h 2)
  · obtain ⟨h1, h2⟩ := deriv_comAngularMomentum_fixedAxisMotion hc hI ω₀ α t
    rw [h1, h2]
    exact hτ

/-- A sign-flipped torque fails: for `c = 0`, inertia `diag(I_xx, I_yy, I_zz)` about it, `I_zz > 0`
and `α ≠ 0`, the constructed motion satisfies neither Euler's equations nor the balance law with
the torque `-τ_B`. -/
lemma fixedAxisMotion_neg_torque {B : RigidBody 3} (hc : B.centerOfMass = 0) {Ixx Iyy Izz : ℝ}
    (hI : B.inertiaTensorAbout B.centerOfMass = Matrix.diagonal ![Ixx, Iyy, Izz]) (hIzz : 0 < Izz)
    {ω₀ α : ℝ} (hα : α ≠ 0) (t : Time) :
    (fixedAxisMotion B ω₀ α).inertiaTensorAbout (fixedAxisMotion B ω₀ α).centerOfMass *ᵥ
          ∂ₜ (fixedAxisMotion B ω₀ α).bodyAngularVelocity t +
        (fixedAxisMotion B ω₀ α).bodyAngularVelocity t ⨯₃
          ((fixedAxisMotion B ω₀ α).inertiaTensorAbout (fixedAxisMotion B ω₀ α).centerOfMass *ᵥ
            (fixedAxisMotion B ω₀ α).bodyAngularVelocity t) ≠
        -fixedAxisTorque Izz α ∧
      ∂ₜ (comAngularMomentum (fixedAxisMotion B ω₀ α)) t ≠ -fixedAxisTorque Izz α := by
  have hne : fixedAxisTorque Izz α ≠ -fixedAxisTorque Izz α := by
    intro h
    have h2 : Izz * α = -(Izz * α) := by simpa [fixedAxisTorque] using congrFun h 2
    exact mul_ne_zero hIzz.ne' hα (by linarith)
  obtain ⟨h1, h2⟩ := deriv_comAngularMomentum_fixedAxisMotion hc hI ω₀ α t
  refine ⟨?_, ?_⟩
  · rw [fixedAxisMotion_euler hI ω₀ α t]
    exact hne
  · rw [h1, h2]
    exact hne

/-! ## G. Torque-free axisymmetric precession -/

/-- The precession rate `ν = (I₃ - I_⊥) ω₃ / I_⊥` of torque-free axisymmetric motion with
transverse principal inertia `I_⊥`, axial principal inertia `I₃` and axial spin `ω₃`. With
`a / 0 = 0` it is `0` when `I_⊥ = 0`; the intended domain is `I_⊥ > 0`. -/
noncomputable def axisymmetricPrecessionRate (Iperp I₃ ω₃ : ℝ) : ℝ := (I₃ - Iperp) * ω₃ / Iperp

/-- The body angular velocity `ω_B(t) = (A cos (ν t), A sin (ν t), ω₃)` of torque-free
axisymmetric motion, with transverse amplitude `A`, axial spin `ω₃` and precession rate
`ν = axisymmetricPrecessionRate I_⊥ I₃ ω₃`. It solves the torque-free Euler equations for
`I_⊥ > 0`; no attitude with this angular velocity is constructed. -/
noncomputable def axisymmetricPrecession (Iperp I₃ A ω₃ : ℝ) (t : Time) : Fin 3 → ℝ :=
  ![A * Real.cos (axisymmetricPrecessionRate Iperp I₃ ω₃ * t.val),
    A * Real.sin (axisymmetricPrecessionRate Iperp I₃ ω₃ * t.val), ω₃]

/-- The witness is differentiable, with `ω_B'(t) = (-A ν sin (ν t), A ν cos (ν t), 0)`. -/
lemma deriv_axisymmetricPrecession (Iperp I₃ A ω₃ : ℝ) (t : Time) :
    DifferentiableAt ℝ (axisymmetricPrecession Iperp I₃ A ω₃) t ∧
      ∂ₜ (axisymmetricPrecession Iperp I₃ A ω₃) t =
        ![-(A * axisymmetricPrecessionRate Iperp I₃ ω₃ *
            Real.sin (axisymmetricPrecessionRate Iperp I₃ ω₃ * t.val)),
          A * axisymmetricPrecessionRate Iperp I₃ ω₃ *
            Real.cos (axisymmetricPrecessionRate Iperp I₃ ω₃ * t.val), 0] := by
  set ν := axisymmetricPrecessionRate Iperp I₃ ω₃ with hν
  have hl : HasDerivAt (fun x : ℝ => ν * x) ν t.val := by
    simpa using (hasDerivAt_id t.val).const_mul ν
  have hc : HasDerivAt (fun x : ℝ => A * Real.cos (ν * x))
      (-(A * ν * Real.sin (ν * t.val))) t.val :=
    (((Real.hasDerivAt_cos (ν * t.val)).comp t.val hl).const_mul A).congr_deriv (by ring)
  have hs : HasDerivAt (fun x : ℝ => A * Real.sin (ν * x))
      (A * ν * Real.cos (ν * t.val)) t.val :=
    (((Real.hasDerivAt_sin (ν * t.val)).comp t.val hl).const_mul A).congr_deriv (by ring)
  have hγ : HasDerivAt (fun x : ℝ => ![A * Real.cos (ν * x), A * Real.sin (ν * x), ω₃])
      ![-(A * ν * Real.sin (ν * t.val)), A * ν * Real.cos (ν * t.val), 0] t.val := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hc
    · simpa using hs
    · simpa using hasDerivAt_const t.val ω₃
  refine ⟨?_, ?_⟩
  · exact hγ.differentiableAt.comp t Time.toRealCLE.differentiableAt
  · exact Time.deriv_comp_toRealCLE_of_hasDerivAt _ t _ hγ

/-- Euler's equations without torque: for `I_⊥ > 0` and the axisymmetric inertia
`I = diag(I_⊥, I_⊥, I₃)`, the witness satisfies `I ω_B' + ω_B × (I ω_B) = 0` at every time. -/
lemma axisymmetricPrecession_euler {Iperp : ℝ} (hIperp : 0 < Iperp) (I₃ A ω₃ : ℝ) (t : Time) :
    Matrix.diagonal ![Iperp, Iperp, I₃] *ᵥ ∂ₜ (axisymmetricPrecession Iperp I₃ A ω₃) t +
        axisymmetricPrecession Iperp I₃ A ω₃ t ⨯₃
          (Matrix.diagonal ![Iperp, Iperp, I₃] *ᵥ axisymmetricPrecession Iperp I₃ A ω₃ t) =
      0 := by
  rw [(deriv_axisymmetricPrecession Iperp I₃ A ω₃ t).2]
  have hne : Iperp ≠ 0 := ne_of_gt hIperp
  ext i
  fin_cases i <;>
    simp [axisymmetricPrecession, axisymmetricPrecessionRate, Matrix.mulVec_diagonal,
      cross_apply] <;>
    field_simp <;>
    ring

/-- The gyroscopic term at `t = 0`: `ω_B(0) = (A, 0, ω₃)`, `I ω_B(0) = (I_⊥ A, 0, I₃ ω₃)` and
`ω_B(0) × (I ω_B(0)) = (0, (I_⊥ - I₃) A ω₃, 0)`. -/
lemma axisymmetricPrecession_gyroscopic_zero (Iperp I₃ A ω₃ : ℝ) :
    axisymmetricPrecession Iperp I₃ A ω₃ 0 ⨯₃
        (Matrix.diagonal ![Iperp, Iperp, I₃] *ᵥ axisymmetricPrecession Iperp I₃ A ω₃ 0) =
      ![0, (Iperp - I₃) * (A * ω₃), 0] := by
  ext i
  fin_cases i <;>
    simp [axisymmetricPrecession, Time.zero_val, Matrix.mulVec_diagonal, cross_apply]
  ring

/-- The gyroscopic term is nonzero at `t = 0` when `I_⊥ ≠ I₃` and `A ω₃ ≠ 0`. -/
lemma axisymmetricPrecession_gyroscopic_ne_zero {Iperp I₃ A ω₃ : ℝ} (hne : Iperp ≠ I₃)
    (hAω : A * ω₃ ≠ 0) :
    axisymmetricPrecession Iperp I₃ A ω₃ 0 ⨯₃
        (Matrix.diagonal ![Iperp, Iperp, I₃] *ᵥ axisymmetricPrecession Iperp I₃ A ω₃ 0) ≠ 0 := by
  rw [axisymmetricPrecession_gyroscopic_zero]
  intro h
  have h1 := congrFun h 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] at h1
  exact mul_ne_zero (sub_ne_zero.mpr hne) hAω h1

/-- The witness tests the Euler port of the torque-balance section: for positive inertias,
`I = diag(I_⊥, I_⊥, I₃)` is positive definite, and the angular acceleration that
`euler_solve_iff` determines without torque, `I⁻¹ (0 - ω_B × (I ω_B))`, is the witness's own
`ω_B'`. -/
lemma axisymmetricPrecession_euler_solve {Iperp I₃ : ℝ} (hIperp : 0 < Iperp) (hI₃ : 0 < I₃)
    (A ω₃ : ℝ) (t : Time) :
    (Matrix.diagonal ![Iperp, Iperp, I₃]).PosDef ∧
      ∂ₜ (axisymmetricPrecession Iperp I₃ A ω₃) t = (Matrix.diagonal ![Iperp, Iperp, I₃])⁻¹ *ᵥ
        (0 - axisymmetricPrecession Iperp I₃ A ω₃ t ⨯₃
          (Matrix.diagonal ![Iperp, Iperp, I₃] *ᵥ axisymmetricPrecession Iperp I₃ A ω₃ t)) := by
  have hpos : (Matrix.diagonal ![Iperp, Iperp, I₃]).PosDef :=
    Matrix.PosDef.diagonal fun i => by fin_cases i <;> simp [hIperp, hI₃]
  refine ⟨hpos, ?_⟩
  exact (euler_solve_iff hpos _ _ 0).mp (axisymmetricPrecession_euler hIperp I₃ A ω₃ t)

end Mechanics.RigidMotionPorts
