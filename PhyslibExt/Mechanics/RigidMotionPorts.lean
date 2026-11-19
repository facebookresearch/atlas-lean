/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Physlib.ClassicalMechanics.RigidBody.AngularVelocity
public import PhyslibExt.Units.EngineeringFrames
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Variable-rate rotating and translating-frame acceleration

The acceleration of a point in a frame that rotates at a variable rate and translates, derived
from Physlib's rigid-body angular velocity.

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

Model inputs (hypotheses of the module):

* `R` (entry by entry), `o` and `x_B` are `C²` on an open set of times containing the interval
  considered;
* time derivatives are Physlib's `∂ₜ`; the statements use only Mathlib's default instances on
  matrices (the product topology), so no matrix norm is chosen;
* orientations are proper rotations, as in Physlib's `RigidBodyMotion`; reflections are not
  admissible.

Non-goals: fictitious forces and the equations of motion in the moving frame, angular momentum,
Euler's equations, attitude parametrizations, and any empirical adequacy or system safety claim.

## ii. Key results

- `deriv_bodyToInertialVec` : the transport law `d(R u)/dt = R (u' + ω_B × u)`.
- `deriv_deriv_bodyToInertial` : the acceleration in a frame with variable rotation rate and
  translating origin.
- `deriv_deriv_bodyToInertial_of_const` : a constant rate and a fixed origin give the
  constant-rate decomposition.
- `orientation_ne_reflectX` : no rigid-body motion has a reflection as an orientation.

## iii. Table of contents

- A. Transport of body components
  - A.1. Private calculus helpers
  - A.2. The transport law
- B. Acceleration in a rotating and translating frame
- C. The reflection boundary

## iv. References

- L. D. Landau and E. M. Lifshitz, *Mechanics*, Sections 31 and 39 (angular velocity; motion in
  a non-inertial frame of reference, with the translational, Euler, Coriolis and centrifugal
  terms).
- H. Goldstein, C. Poole and J. Safko, *Classical Mechanics*, 3rd edition, 2002, Sections 4.9
  and 4.10 (rate of change of a vector; the Coriolis effect).
- Physlib's `RigidBodyMotion.bodyAngularVelocity` and
  `RigidBodyMotion.deriv_orientation_mulVec_eq_orientation_bodyAngularVelocity_cross`, and the
  frame dictionary `PhyslibExt.Units.EngineeringFrames`.
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

/-! ## C. The reflection boundary -/

/-- Reflections are inadmissible: no rigid-body motion has the reflection `diag(-1, 1, 1)` as an
orientation. -/
lemma orientation_ne_reflectX (M : RigidBodyMotion 3) (t : Time) :
    (M.orientation t : Matrix (Fin 3) (Fin 3) ℝ) ≠ reflectX := by
  intro h
  have hdet := (Matrix.mem_specialOrthogonalGroup_iff.mp (M.orientation t).2).2
  rw [h] at hdet
  simp [reflectX, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  norm_num at hdet

end Mechanics.RigidMotionPorts
