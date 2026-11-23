/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Physlib.ClassicalMechanics.RigidBody.Motion
public import PhyslibExt.CondensedMatter.Elasticity.StressStrain
public import PhyslibExt.Units.EngineeringQuantities
import MathlibExt.LinearAlgebra.CrossProduct

/-!
# Body-to-inertial frame convention and engineering sign dictionary

One frame convention `x_I = o + R x_B` with `R ∈ SO(3)`, its active and passive component maps,
the tension-positive mean pressure `p = -tr σ / 3` and the degree-to-radian factor `π / 180`,
stated with the engineering dimensions and fixtures of `PhyslibExt.Units.EngineeringQuantities`.

## i. Overview

A body frame is given by the inertial coordinates `o` of its origin and an orientation
`R : Matrix.specialOrthogonalGroup (Fin 3) ℝ`, the carrier Physlib's `RigidBodyMotion` uses; the
columns of `R` are the body axes in inertial components. A point with body coordinates `x_B` has
inertial coordinates `x_I = o + R x_B` (`bodyToInertial`), and the inverse map is
`x_I ↦ Rᵀ (x_I - o)` (`inertialToBody`). Physlib's `RigidBodyMotion.displacement` is this map
with `o` the centre-of-mass position and `x_B` the position relative to the centre of mass
(`displacement_eq_bodyToInertial`). No second rotation type is introduced.

Free vectors (forces, velocities, moments) carry no origin. Their passive component maps are
`v_I = R v_B` (`bodyToInertialVec`) and `v_B = Rᵀ v_I` (`inertialToBodyVec`); the active rotation
of a vector within one frame is `v ↦ R v` (`rotateActive`). The passive map to inertial
components agrees with the active rotation by `R`, and the passive map to body components is the
active rotation by `R⁻¹ = Rᵀ`: turning the frame by `R` turns components by the inverse.

Moments transfer with the orientation, `R (a ⨯₃ b) = (R a) ⨯₃ (R b)`; this is the determinant-one
case of the existing law `(Q a) ⨯₃ (Q b) = det Q • Q (a ⨯₃ b)` for orthogonal `Q`
(`Matrix.mulVec_cross_mulVec_of_mem_orthogonalGroup`). A reflection of determinant
`-1` reverses cross-product orientation and is not a frame orientation. Torque and energy share
the dimension `M L² T⁻²`, but torque components change with the frame while work-type dot
products do not.

Stress tensors are written with tension positive, and the mean pressure is
`p = -σₘ = -tr σ / 3`, the negative of the existing mean stress `Elasticity.meanStress`: the
hydrostatic stress `-p 1` has pressure `p`, and a uniaxial tension has negative pressure. The
mean pressure is the same in body and inertial components (`σ_I = R σ_B Rᵀ`) and carries the
stress unit. An angle of `θ` degrees is `θ π / 180` radians (`degToRad`); this factor is applied
explicitly, since no change of unit scale rescales a dimensionless coordinate.

Model inputs (hypotheses of the module):

* every orientation is proper orthogonal, `R ∈ SO(3)`, and the inverse component map is `Rᵀ`;
* the origin `o` is an explicit argument, and all coordinates of points are in one explicit
  length unit; changing that unit rescales origin, body and inertial coordinates alike;
* stresses are tension-positive Cauchy stress components in an orthonormal frame.

Non-goals: no new rotation or frame type, no angle type (a degree reading converts by the
explicit factor `degToRad`), no Euler-angle parametrization, no moment transport between
arbitrary reference points, no frame kinematics beyond Physlib's, and no empirical adequacy or
system safety claim.

## ii. Key results

- `bodyToInertial`, `inertialToBody`, `bodyToInertialVec`, `inertialToBodyVec`, `rotateActive` :
  the frame dictionary, with `inertialToBody_bodyToInertial`, `bodyToInertial_inertialToBody`,
  `inertialToBodyVec_bodyToInertialVec`, `bodyToInertialVec_inertialToBodyVec`,
  `bodyToInertial_sub_bodyToInertial`, `bodyToInertialVec_eq_rotateActive`,
  `inertialToBodyVec_eq_rotateActive_inv` and `bodyToInertial_dimScale`.
- `displacement_eq_bodyToInertial`, `inertialToBody_displacement` : Physlib's rigid-body motions
  follow this convention.
- `bodyToInertialVec_cross`, `bodyToInertialVec_moment`, `bodyToInertialVec_dotProduct` : moments
  transfer with the orientation, and dot products are frame independent.
- `meanPressure`, `meanPressure_eq`, `meanPressure_neg_smul_one`, `meanPressure_uniaxial`,
  `meanPressure_conj`, `meanPressure_dimScale` : the tension-positive mean pressure.
- `degToRad`, `degToRad_ninety`, `degToRad_ne_dimScale_one_mul`, `rotZ`,
  `rotZ_mem_specialOrthogonalGroup`, `rotZ_degToRad_ninety` : the degree factor and the rotation
  about the third axis.
- `quarterTurnZ_fixture`, `bodyToInertial_quarterTurnZ_si_mm`,
  `bodyToInertialVec_quarterTurnZ_moment_ne`,
  `reflectX_mem_orthogonalGroup`, `reflectX_not_mem_specialOrthogonalGroup`, `reflectX_cross`,
  `reflectX_cross_fixture` : the quarter-turn fixture and the reflection boundary.

## iii. Table of contents

- A. The body-to-inertial convention
- B. Physlib rigid-body motions use this convention
- C. Moments and work
- D. Mean pressure of a tension-positive stress
- E. Degrees and the rotation about the third axis
- F. Quarter-turn fixtures and the reflection boundary

## iv. References

- L. D. Landau and E. M. Lifshitz, *Mechanics*, Section 32: the motion of a rigid body as a
  translation of its centre of mass and a rotation about it.
- ISO 80000-3, *Quantities and units — Part 3: Space and time*: plane angle and the degree
  `π / 180` rad.
- ISO 80000-4, *Quantities and units — Part 4: Mechanics*: normal stress, pressure and torque.
- Mathlib's `Matrix.specialOrthogonalGroup` and `crossProduct`, Physlib's `RigidBodyMotion`,
  `PhyslibExt.CondensedMatter.Elasticity.StressStrain` and `PhyslibExt.Units.EngineeringQuantities`
  at the root package's pin.
-/

@[expose] public section

open Dimension Units.QuantityDimensions Units.EngineeringQuantities
open scoped Matrix

namespace Units.EngineeringFrames

/-! ## A. The body-to-inertial convention -/

/-- The inertial coordinates `x_I = o + R x_B` of the point with body coordinates `x_B`, for a
body frame whose origin has inertial coordinates `o` and whose orientation is `R ∈ SO(3)`. -/
def bodyToInertial (o : Fin 3 → ℝ) (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (xB : Fin 3 → ℝ) : Fin 3 → ℝ :=
  o + (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ xB

/-- The body coordinates `x_B = Rᵀ (x_I - o)` of the point with inertial coordinates `x_I`. -/
def inertialToBody (o : Fin 3 → ℝ) (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (xI : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *ᵥ (xI - o)

/-- The passive component map of a free vector (a force, a velocity, a moment): the inertial
components `v_I = R v_B` of the vector with body components `v_B`. No origin enters. -/
def bodyToInertialVec (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (vB : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ vB

/-- The passive component map back: the body components `v_B = Rᵀ v_I` of the free vector with
inertial components `v_I`. -/
def inertialToBodyVec (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (vI : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *ᵥ vI

/-- The active rotation of a vector by `R`: the rotated vector, with both vectors expressed in
one frame. -/
def rotateActive (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v

/-- The passive map to inertial components agrees with the active rotation by `R`. -/
lemma bodyToInertialVec_eq_rotateActive (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (v : Fin 3 → ℝ) : bodyToInertialVec R v = rotateActive R v := by
  rfl

/-- The passive map to body components is the active rotation by `R⁻¹`: turning the frame by `R`
turns components by the inverse. -/
lemma inertialToBodyVec_eq_rotateActive_inv (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (v : Fin 3 → ℝ) : inertialToBodyVec R v = rotateActive R⁻¹ v := by
  simp only [inertialToBodyVec, rotateActive]
  congr 1

/-- The inverse of `x_B ↦ o + R x_B` is `x_I ↦ Rᵀ (x_I - o)`: body coordinates are recovered. -/
lemma inertialToBody_bodyToInertial (o : Fin 3 → ℝ)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (xB : Fin 3 → ℝ) :
    inertialToBody o R (bodyToInertial o R xB) = xB := by
  have hT : (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * R = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  simp only [inertialToBody, bodyToInertial, add_sub_cancel_left, Matrix.mulVec_mulVec, hT,
    Matrix.one_mulVec]

/-- Inertial coordinates are recovered from body coordinates. -/
lemma bodyToInertial_inertialToBody (o : Fin 3 → ℝ)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (xI : Fin 3 → ℝ) :
    bodyToInertial o R (inertialToBody o R xI) = xI := by
  have hT : (R : Matrix (Fin 3) (Fin 3) ℝ) * (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  simp only [inertialToBody, bodyToInertial, Matrix.mulVec_mulVec, hT, Matrix.one_mulVec,
    add_sub_cancel]

/-- The passive map to body components inverts the passive map to inertial components. -/
lemma inertialToBodyVec_bodyToInertialVec (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (vB : Fin 3 → ℝ) : inertialToBodyVec R (bodyToInertialVec R vB) = vB := by
  have hT : (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * R = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  simp only [inertialToBodyVec, bodyToInertialVec, Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]

/-- The passive map to inertial components inverts the passive map to body components. -/
lemma bodyToInertialVec_inertialToBodyVec (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (vI : Fin 3 → ℝ) : bodyToInertialVec R (inertialToBodyVec R vI) = vI := by
  have hT : (R : Matrix (Fin 3) (Fin 3) ℝ) * (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  simp only [inertialToBodyVec, bodyToInertialVec, Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]

/-- The displacement between two points is a free vector: the frame origin cancels. -/
lemma bodyToInertial_sub_bodyToInertial (o : Fin 3 → ℝ)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x y : Fin 3 → ℝ) :
    bodyToInertial o R x - bodyToInertial o R y = bodyToInertialVec R (x - y) := by
  simp only [bodyToInertial, bodyToInertialVec, Matrix.mulVec_sub, add_sub_add_left_eq_sub]

/-- Units are explicit: expressing the origin and the body coordinates in a new length unit
rescales the inertial coordinates by the same length factor. -/
lemma bodyToInertial_dimScale (u1 u2 : UnitScale ISQDimensionBase) (o : Fin 3 → ℝ)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (xB : Fin 3 → ℝ) :
    bodyToInertial ((u1.dimScale u2 (single .length) : ℝ) • o) R
        ((u1.dimScale u2 (single .length) : ℝ) • xB) =
      (u1.dimScale u2 (single .length) : ℝ) • bodyToInertial o R xB := by
  simp only [bodyToInertial, Matrix.mulVec_smul, smul_add]

/-! ## B. Physlib rigid-body motions use this convention -/

/-- At time `t`, Physlib's rigid displacement places the body point `y` at `x_I = o + R x_B`,
with `o` the inertial position of the centre of mass, `R` the orientation and `x_B = y - c` the
coordinates of `y` relative to the centre of mass `c`. -/
lemma displacement_eq_bodyToInertial (M : RigidBodyMotion 3) (t : Time) (y : Space 3) :
    (fun k => M.displacement t y k) =
      bodyToInertial (fun k => M.comTrajectory t k) (M.orientation t)
        (fun j => y j - M.centerOfMass j) := by
  funext k
  rw [RigidBodyMotion.displacement_apply]
  simp only [bodyToInertial, Pi.add_apply, Matrix.mulVec, dotProduct]
  ring

/-- The body coordinates of a displaced body point are its coordinates relative to the centre
of mass. -/
lemma inertialToBody_displacement (M : RigidBodyMotion 3) (t : Time) (y : Space 3) :
    inertialToBody (fun k => M.comTrajectory t k) (M.orientation t)
        (fun k => M.displacement t y k) =
      fun j => y j - M.centerOfMass j := by
  rw [displacement_eq_bodyToInertial, inertialToBody_bodyToInertial]

/-! ## C. Moments and work -/

/-- Moments transfer between frames with the orientation: the inertial components of `a ⨯₃ b`
are the cross product of the inertial components of `a` and `b`. -/
lemma bodyToInertialVec_cross (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (a b : Fin 3 → ℝ) :
    bodyToInertialVec R (a ⨯₃ b) = bodyToInertialVec R a ⨯₃ bodyToInertialVec R b := by
  have hR := Matrix.mem_specialOrthogonalGroup_iff.mp R.2
  simp only [bodyToInertialVec]
  rw [Matrix.mulVec_cross_mulVec_of_mem_orthogonalGroup hR.1 a b, hR.2, one_smul]

/-- The moment `x_B ⨯₃ F_B` about the body origin of the force `F_B` applied at the body point
`x_B` has inertial components `(x_I - o) ⨯₃ F_I`: its lever arm runs from the explicit origin
`o` of the body frame. -/
lemma bodyToInertialVec_moment (o : Fin 3 → ℝ) (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (xB FB : Fin 3 → ℝ) :
    bodyToInertialVec R (xB ⨯₃ FB) = (bodyToInertial o R xB - o) ⨯₃ bodyToInertialVec R FB := by
  rw [bodyToInertialVec_cross]
  congr 1
  simp only [bodyToInertial, bodyToInertialVec, add_sub_cancel_left]

/-- Work-type scalars are frame independent: the dot product of two vectors, such as the work
`F ⬝ᵥ d` of a force along a displacement, is the same in body and inertial components. -/
lemma bodyToInertialVec_dotProduct (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (a b : Fin 3 → ℝ) : bodyToInertialVec R a ⬝ᵥ bodyToInertialVec R b = a ⬝ᵥ b := by
  have hT : (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * R = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  simp only [bodyToInertialVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hT,
    Matrix.one_mulVec]

/-! ## D. Mean pressure of a tension-positive stress -/

/-- The mean pressure `p = -σₘ` of a stress tensor `σ` written with the tension-positive sign
convention: the negative of the mean stress `Elasticity.meanStress σ = tr σ / 3`. -/
noncomputable def meanPressure (σ : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := -Elasticity.meanStress σ

/-- The mean pressure of a tension-positive stress is `p = -tr σ / 3`. -/
lemma meanPressure_eq (σ : Matrix (Fin 3) (Fin 3) ℝ) :
    meanPressure σ = -Matrix.trace σ / 3 := by
  simp only [meanPressure, Elasticity.meanStress]
  ring

/-- The hydrostatic stress `σ = -p 1` has mean pressure `p`. -/
lemma meanPressure_neg_smul_one (p : ℝ) :
    meanPressure (-(p • (1 : Matrix (Fin 3) (Fin 3) ℝ))) = p := by
  simp [meanPressure, Elasticity.meanStress, Matrix.trace_neg, Matrix.trace_smul, Matrix.trace_one]
  ring

/-- A uniaxial tension `s` has mean pressure `-s / 3`, negative for `s > 0`: with tension
positive, a tension lowers the pressure. -/
lemma meanPressure_uniaxial (s : ℝ) : meanPressure (Matrix.diagonal ![s, 0, 0]) = -s / 3 := by
  simp [meanPressure, Elasticity.meanStress, Matrix.trace, Fin.sum_univ_three]
  ring

/-- The mean pressure is the same in body and inertial components: stress components transform
as `σ_I = R σ_B Rᵀ`. -/
lemma meanPressure_conj (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (σ : Matrix (Fin 3) (Fin 3) ℝ) :
    meanPressure ((R : Matrix (Fin 3) (Fin 3) ℝ) * σ * (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) =
      meanPressure σ := by
  have hT : (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * R = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  simp only [meanPressure, Elasticity.meanStress]
  rw [Elasticity.trace_conjugate σ _ hT]

/-- The mean pressure carries the stress unit: rescaling every stress component by the stress
factor rescales the mean pressure by the same factor. -/
lemma meanPressure_dimScale (u1 u2 : UnitScale ISQDimensionBase)
    (σ : Matrix (Fin 3) (Fin 3) ℝ) :
    meanPressure ((u1.dimScale u2 stressDim : ℝ) • σ) =
      (u1.dimScale u2 stressDim : ℝ) * meanPressure σ := by
  simp only [meanPressure, Elasticity.meanStress, Matrix.trace_smul]
  ring

/-! ## E. Degrees and the rotation about the third axis -/

/-- The radian measure `θ π / 180` of an angle of `θ` degrees. -/
noncomputable def degToRad (θ : ℝ) : ℝ := θ * Real.pi / 180

/-- Ninety degrees is `π / 2` radians. -/
lemma degToRad_ninety : degToRad 90 = Real.pi / 2 := by
  unfold degToRad
  ring

/-- The degree conversion is an explicit factor, never a change of unit scale: it moves every
nonzero reading, while a dimensionless coordinate does not rescale under any change of
`UnitScale`. -/
lemma degToRad_ne_dimScale_one_mul (u1 u2 : UnitScale ISQDimensionBase) {θ : ℝ} (hθ : θ ≠ 0) :
    degToRad θ ≠ (u1.dimScale u2 1 : ℝ) * θ := by
  rw [dimScale_one_mul]
  unfold degToRad
  intro h
  have h1 : θ * Real.pi = θ * 180 := by
    linarith [h, show θ * Real.pi / 180 * 180 = θ * Real.pi by ring]
  have h2 : Real.pi = 180 := mul_left_cancel₀ hθ h1
  linarith [Real.pi_le_four]

/-- The rotation matrix by the angle `θ` (in radians) about the third axis. -/
noncomputable def rotZ (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]

/-- The rotation about the third axis is proper orthogonal. -/
lemma rotZ_mem_specialOrthogonalGroup (θ : ℝ) :
    rotZ θ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three] <;>
      nlinarith [Real.cos_sq_add_sin_sq θ]
  · simp [rotZ, Matrix.det_fin_three]
    nlinarith [Real.cos_sq_add_sin_sq θ]

/-- At ninety degrees the rotation about the third axis is the quarter turn `e₁ ↦ e₂`,
`e₂ ↦ -e₁`, `e₃ ↦ e₃`. -/
lemma rotZ_degToRad_ninety : rotZ (degToRad 90) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
  rw [degToRad_ninety]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotZ, Real.cos_pi_div_two, Real.sin_pi_div_two]

/-! ## F. Quarter-turn fixtures and the reflection boundary -/

/-- The ninety-degree rotation about the third axis, as a frame orientation. -/
noncomputable def quarterTurnZ : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨rotZ (degToRad 90), rotZ_mem_specialOrthogonalGroup _⟩

/-- The quarter turn on the nonparallel pair `e₁, e₂`: their inertial components are `e₂` and
`-e₁`; the moment `e₁ ⨯₃ e₂ = e₃` has inertial components `e₃`, the cross product of the
transferred pair; and the passive map to body components turns `e₁` to `-e₂`, the opposite way
from the active rotation, which turns it to `e₂`. -/
lemma quarterTurnZ_fixture :
    bodyToInertialVec quarterTurnZ ![1, 0, 0] = ![0, 1, 0] ∧
      bodyToInertialVec quarterTurnZ ![0, 1, 0] = ![-1, 0, 0] ∧
      bodyToInertialVec quarterTurnZ (![1, 0, 0] ⨯₃ ![0, 1, 0]) = ![0, 0, 1] ∧
      bodyToInertialVec quarterTurnZ ![1, 0, 0] ⨯₃ bodyToInertialVec quarterTurnZ ![0, 1, 0] =
        ![0, 0, 1] ∧
      rotateActive quarterTurnZ ![1, 0, 0] = ![0, 1, 0] ∧
      inertialToBodyVec quarterTurnZ ![1, 0, 0] = ![0, -1, 0] := by
  have hq : (quarterTurnZ : Matrix (Fin 3) (Fin 3) ℝ) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] :=
    rotZ_degToRad_ninety
  simp only [bodyToInertialVec, rotateActive, inertialToBodyVec, hq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, cross_apply]

/-- Units and the origin are explicit: the body point `(1, 0, 0)` of the quarter-turned frame with
origin `(2, 0, 0)` lies at `(2, 1, 0)` (metres); from metres to millimetres the length factor is
`1000`, and the origin `(2000, 0, 0)` and the body point `(1000, 0, 0)` give `(2000, 1000, 0)`. -/
lemma bodyToInertial_quarterTurnZ_si_mm :
    bodyToInertial ![2, 0, 0] quarterTurnZ ![1, 0, 0] = ![2, 1, 0] ∧
      (siScale.dimScale mmScale (single .length) : ℝ) = 1000 ∧
      bodyToInertial ![2000, 0, 0] quarterTurnZ ![1000, 0, 0] = ![2000, 1000, 0] := by
  have hq : (quarterTurnZ : Matrix (Fin 3) (Fin 3) ℝ) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] :=
    rotZ_degToRad_ninety
  refine ⟨?_, ?_, ?_⟩
  · simp only [bodyToInertial, hq]
    ext i
    fin_cases i <;> simp
  · rw [dimScale_single]
    simp [siScale, mmScale]
  · simp only [bodyToInertial, hq]
    ext i
    fin_cases i <;> simp

/-- Torque is not a scalar energy merely because the dimensions agree: under the quarter turn the
moment `e₂ ⨯₃ e₃ = e₁` has inertial components `e₂`, so its components change with the frame,
unlike the frame-independent dot products of `bodyToInertialVec_dotProduct`. -/
lemma bodyToInertialVec_quarterTurnZ_moment_ne :
    bodyToInertialVec quarterTurnZ (![0, 1, 0] ⨯₃ ![0, 0, 1]) ≠ ![0, 1, 0] ⨯₃ ![0, 0, 1] := by
  have hq : (quarterTurnZ : Matrix (Fin 3) (Fin 3) ℝ) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] :=
    rotZ_degToRad_ninety
  simp only [bodyToInertialVec, hq]
  intro h
  have h0 := congrFun h 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, cross_apply] at h0

/-- The reflection `diag(-1, 1, 1)`, which reverses the first axis. -/
def reflectX : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![-1, 1, 1]

/-- The reflection is orthogonal. -/
lemma reflectX_mem_orthogonalGroup : reflectX ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflectX, Matrix.diagonal, Matrix.mul_apply]

/-- The reflection has determinant `-1`, so it is not a frame orientation. -/
lemma reflectX_not_mem_specialOrthogonalGroup :
    reflectX ∉ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  intro h
  have hdet := (Matrix.mem_specialOrthogonalGroup_iff.mp h).2
  simp [reflectX, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  norm_num at hdet

/-- A determinant `-1` reflection reverses cross-product orientation:
`(P a) ⨯₃ (P b) = -(P (a ⨯₃ b))`. -/
lemma reflectX_cross (a b : Fin 3 → ℝ) :
    (reflectX *ᵥ a) ⨯₃ (reflectX *ᵥ b) = -(reflectX *ᵥ (a ⨯₃ b)) := by
  have horth : reflectX ∈ Matrix.orthogonalGroup (Fin 3) ℝ := reflectX_mem_orthogonalGroup
  have hdet : reflectX.det = -1 := by
    simp [reflectX, Matrix.det_diagonal, Fin.prod_univ_three]
  rw [Matrix.mulVec_cross_mulVec_of_mem_orthogonalGroup horth a b, hdet, neg_one_smul]

/-- On `e₁, e₂` the reflection gives `(P e₁) ⨯₃ (P e₂) = -e₃` but `P (e₁ ⨯₃ e₂) = e₃`. -/
lemma reflectX_cross_fixture :
    (reflectX *ᵥ ![1, 0, 0]) ⨯₃ (reflectX *ᵥ ![0, 1, 0]) = ![0, 0, -1] ∧
      reflectX *ᵥ (![1, 0, 0] ⨯₃ ![0, 1, 0]) = ![0, 0, 1] := by
  refine ⟨?_, ?_⟩ <;> ext i <;> fin_cases i <;>
    simp [reflectX, Matrix.mulVec_diagonal, cross_apply]

end Units.EngineeringFrames
