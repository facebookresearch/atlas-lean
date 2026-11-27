/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Physlib.ClassicalMechanics.EulerLagrange
public import PhyslibExt.Units.EngineeringFrames
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Two-link kinetic energy, mass matrix, rod reactions and reduced equation of motion

A planar open double pendulum: point masses `m₁, m₂ > 0` on massless rods of lengths
`l₁, l₂ > 0`, the first rod pivoted at the origin and the second at the first mass. The
generalized coordinates are the absolute link angles `q₁, q₂`, each measured counterclockwise
from the downward vertical, with the second Cartesian axis pointing up.

## i. Overview

The positions in the Euclidean plane are `p₁ = l₁ (sin q₁, -cos q₁)` and
`p₂ = p₁ + l₂ (sin q₂, -cos q₂)`; they satisfy the rod constraints `‖p₁‖ = l₁` and
`‖p₂ - p₁‖ = l₂`. In the frame dictionary of `PhyslibExt.Units.EngineeringFrames` each link is a
body frame with origin at its pivot and orientation `rotZ qᵢ`, with its mass at body coordinates
`(0, -lᵢ, 0)`; the second angle is not measured from the first link.

Along an angle trajectory with angular velocities `w₁, w₂` the Cartesian velocities are the
actual time derivatives of the positions, and the kinetic energy `m₁ ‖ṗ₁‖² / 2 + m₂ ‖ṗ₂‖² / 2`
(the particle kinetic energy of `PhyslibExt.Mechanics.PowerPorts`, one term per mass) is
`wᵀ M(q) w / 2` for the reduced mass matrix

`M(q) = [[(m₁ + m₂) l₁², m₂ l₁ l₂ cos (q₁ - q₂)], [m₂ l₁ l₂ cos (q₁ - q₂), m₂ l₂²]]`.

With gravity `g` along the downward vertical the potential energy is
`V = g (m₁ y₁ + m₂ y₂) = -(m₁ + m₂) g l₁ cos q₁ - m₂ g l₂ cos q₂` and the Lagrangian is
`L = T - V`. The determinant is `det M = l₁² l₂² m₂ (m₁ + m₂ sin² (q₁ - q₂))`: positive for
positive masses and lengths in every configuration, collinear links included, and zero when a
length vanishes. Every nonzero angular velocity then has positive kinetic energy.

On Cartesian configurations `p = (p₁, p₂)` the rods are the constraints
`g(p) = (‖p₁‖² - l₁², ‖p₂ - p₁‖² - l₂²) = 0`, with Jacobian
`Dg(p) (v₁, v₂) = (2 ⟪p₁, v₁⟫, 2 ⟪p₂ - p₁, v₂ - v₁⟫)`. At every configuration of the angle map
`posMap q = (p₁, p₂)`, collinear links included, the Jacobian has rank two. The angle derivative
`D posMap (q)` is injective with range the kernel of `Dg(posMap q)`; every velocity of a
constrained curve lies in that kernel, and every kernel vector is the velocity of the explicit
constrained curve `s ↦ posMap (q + s w)` for exactly one angular velocity `w`. Rod-normal
reactions `(c₁ p₁ - c₂ (p₂ - p₁), c₂ (p₂ - p₁))` do no virtual work along the kernel, and every
force pair that does no virtual work along it is such a reaction, with unique multipliers; a
positive rod tension is a negative multiplier. A closed chain behaves differently: one point on
two unit circles tangent at `(1, 0)` has a constraint Jacobian of rank one there.

The Euler-Lagrange operator `ClassicalMechanics.eulerLagrangeOp L q = ∂L/∂q - ∂ₜ (∂L/∂v)` of Physlib
takes values in a real inner product space, so there the angles and angular velocities are vectors
of `EuclideanSpace ℝ (Fin 2)`. Along an angle trajectory that is `C²` at `t` the operator is
`f(q, q̇) - M(q) q̈` with the generalized force
`f₁ = -m₂ l₁ l₂ sin (q₁ - q₂) q̇₂² - (m₁ + m₂) g l₁ sin q₁`,
`f₂ = m₂ l₁ l₂ sin (q₁ - q₂) q̇₁² - m₂ g l₂ sin q₂`; for positive masses and lengths the
Euler-Lagrange equation is the reduced ODE `q̈ = M(q)⁻¹ f(q, q̇)`, written out by Cramer's rule.
Newton's equations `mᵢ p̈ᵢ = mᵢ (0, -g) + Rᵢ` along the Cartesian motion `posMap (q t)` hold with a
rod reaction `R` exactly when the angles satisfy the reduced ODE, and then the rod multipliers are
unique. The first-order field `(q, w) ↦ (w, M(q)⁻¹ f(q, w))` is smooth, collinear links included,
so every initial angle and angular velocity starts a solution on an open time interval, along
which the Euler-Lagrange operator vanishes.

Model inputs: point masses on ideal massless rods; absolute link angles in one inertial frame, a
chosen coordinate model on all of `ℝ²` (periodic, not a global chart of the configuration
manifold), with tangent spaces taken locally at a supplied configuration; uniform gravity along
the downward vertical; no friction and no actuation. Virtual velocities are the kernel vectors of
the constraint Jacobian, and a reaction is ideal when it does no virtual work along them
(d'Alembert's principle). Newton's second law holds for each mass, with gravity and the rod
reactions as the only forces. Not treated: global existence or uniqueness for the initial value
problem, closed chains, the lift of an arbitrary constrained Cartesian motion to angles, general
constant-rank or manifold constraints, chart-free or differential-algebraic formulations, the
variational characterization of the Euler-Lagrange operator, numerical integration, and empirical
adequacy or system safety.

## ii. Key results

- `pos_rod_constraints`: the positions satisfy the two rod constraints.
- `toSpace_pos_eq_bodyToInertial`: the absolute link angles in the frame dictionary.
- `hasDerivAt_pos`, `kineticEnergy_actual`: the Cartesian velocities and the kinetic energy on
  actual angle trajectories.
- `kineticEnergy_eq_massMatrix`, `potentialEnergy_eq`, `lagrangian_eq`: the kinetic energy as
  the quadratic form of the reduced mass matrix, the potential energy and the Lagrangian.
- `massMatrix_det`, `massMatrix_det_pos`, `kineticEnergy_pos`: the determinant, its positivity
  and the positive kinetic metric.
- `massMatrix_det_of_collinear`, `massMatrix_det_eq_zero_of_length_eq_zero`: collinear links stay
  regular, and a zero length makes the matrix singular.
- `rodConstraint_posMap`, `hasFDerivAt_rodConstraint`, `hasFDerivAt_posMap`: the angle map
  satisfies the rod constraints, whose Jacobian and the angle derivative are actual derivatives.
- `rodJacobian_rank_two`: the constraint Jacobian has rank two at every configuration of the open
  chain, collinear links included.
- `ker_angleJacobian`, `range_angleJacobian`, `rodJacobian_velocity_eq_zero`,
  `existsUnique_hasDerivAt_posMap`: the angle derivative identifies the angular velocities with
  the kernel of the constraint Jacobian, the velocities of constrained motions.
- `virtualWork_rodReaction_eq_zero`, `existsUnique_rodReaction`: rod-normal reactions do no
  virtual work, and they are the only force pairs that do none, with unique multipliers.
- `eulerLagrangeOp_angleLagrangian`, `eulerLagrangeOp_angleLagrangian_eq_zero_iff`,
  `reducedAccel_eq_inv_mulVec`: the Euler-Lagrange operator is `f(q, q̇) - M(q) q̈`, and its
  vanishing is the reduced ODE `q̈ = M(q)⁻¹ f(q, q̇)`.
- `exists_rodReaction_newton_iff`, `existsUnique_rodReaction_newton_iff`: Newton's equations with
  rod reactions hold exactly along solutions of the reduced ODE, with unique multipliers.
- `contDiff_reducedField`, `locallyLipschitz_reducedField`,
  `exists_forall_mem_Ioo_hasDerivAt_reducedField`, `exists_eulerLagrangeOp_angleLagrangian_eq_zero`:
  the reduced field is smooth and locally Lipschitz, and every initial state starts a local
  solution of the Euler-Lagrange equation.

## iii. Table of contents

- A. Cartesian positions, rod constraints and the frame convention
- B. Velocities on actual angle trajectories
- C. Kinetic energy, potential energy and the Lagrangian
- D. The reduced mass matrix is regular
- E. The rod constraints and their Jacobian
- F. The tangent space
- G. Rod reactions and virtual work
- H. The reduced Euler-Lagrange equation
- I. Newton's equations with rod reactions
- J. Local regularity and the local initial value problem

## iv. References

- L. D. Landau and E. M. Lifshitz, *Mechanics*, Section 5, Problem 1 (the Lagrangian of a
  coplanar double pendulum).
- H. Goldstein, C. Poole and J. Safko, *Classical Mechanics*, 3rd edition, chapter 1
  (constraints, generalized coordinates, and the kinetic energy as a quadratic form in the
  generalized velocities; Sections 1.3 and 1.4 for virtual displacements, d'Alembert's principle
  and workless constraint forces).
- E. A. Coddington and N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 1 (local
  existence by successive approximations).
- `PhyslibExt.Units.EngineeringFrames` (frame convention) and `PhyslibExt.Mechanics.PowerPorts`
  (particle kinetic energy).
- Physlib `ClassicalMechanics.eulerLagrangeOp` (the Euler-Lagrange operator) and Mathlib
  `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` (the Picard-Lindelöf theorem).
-/

@[expose] public section

namespace PhyslibExt.Mechanics.ConstrainedTwoLink

open Units.EngineeringFrames
open scoped Matrix

/-! ## A. Cartesian positions, rod constraints and the frame convention -/

/-- Position of the first point mass, at the tip of the first link of length `l₁` at the absolute
angle `q₁` from the downward vertical: `p₁ = l₁ (sin q₁, -cos q₁)`. -/
noncomputable def pos₁ (l₁ q₁ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  l₁ • !₂[Real.sin q₁, -Real.cos q₁]

/-- Position of the second point mass, at the tip of the second link of length `l₂` at the
absolute angle `q₂`: `p₂ = p₁ + l₂ (sin q₂, -cos q₂)`. -/
noncomputable def pos₂ (l₁ l₂ q₁ q₂ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  pos₁ l₁ q₁ + l₂ • !₂[Real.sin q₂, -Real.cos q₂]

private lemma norm_unit_sin_cos_sq (q : ℝ) : ‖!₂[Real.sin q, -Real.cos q]‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp

private lemma norm_unit_sin_cos (q : ℝ) : ‖!₂[Real.sin q, -Real.cos q]‖ = 1 := by
  have hsq := norm_unit_sin_cos_sq q
  calc ‖!₂[Real.sin q, -Real.cos q]‖
      = Real.sqrt (‖!₂[Real.sin q, -Real.cos q]‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = 1 := by rw [hsq, Real.sqrt_one]

/-- For nonnegative lengths the positions satisfy the two rod constraints `‖p₁‖ = l₁` and
`‖p₂ - p₁‖ = l₂`. -/
lemma pos_rod_constraints {l₁ l₂ : ℝ} (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (q₁ q₂ : ℝ) :
    ‖pos₁ l₁ q₁‖ = l₁ ∧ ‖pos₂ l₁ l₂ q₁ q₂ - pos₁ l₁ q₁‖ = l₂ := by
  constructor
  · unfold pos₁
    rw [norm_smul, norm_unit_sin_cos, mul_one, Real.norm_eq_abs, abs_of_nonneg hl₁]
  · unfold pos₂
    rw [add_sub_cancel_left, norm_smul, norm_unit_sin_cos, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hl₂]

/-- The plane of the pendulum as the first two coordinates of the frame dictionary's space. -/
def toSpace (p : EuclideanSpace ℝ (Fin 2)) : Fin 3 → ℝ :=
  ![p 0, p 1, 0]

/-- Absolute link angles in the frame dictionary: link `i` is the body frame with origin at its
pivot and orientation `rotZ qᵢ`, and its mass sits at body coordinates `(0, -lᵢ, 0)`. -/
lemma toSpace_pos_eq_bodyToInertial (l₁ l₂ q₁ q₂ : ℝ) :
    toSpace (pos₁ l₁ q₁) =
        bodyToInertial 0 ⟨rotZ q₁, rotZ_mem_specialOrthogonalGroup q₁⟩ ![0, -l₁, 0] ∧
      toSpace (pos₂ l₁ l₂ q₁ q₂) =
        bodyToInertial (toSpace (pos₁ l₁ q₁)) ⟨rotZ q₂, rotZ_mem_specialOrthogonalGroup q₂⟩
          ![0, -l₂, 0] := by
  constructor
  · ext i; fin_cases i <;> simp [toSpace, pos₁, bodyToInertial, rotZ]
  · ext i; fin_cases i <;> simp [toSpace, pos₁, pos₂, bodyToInertial, rotZ]

/-! ## B. Velocities on actual angle trajectories -/

/-- Velocity of the first point mass at angle `q₁` and angular velocity `w₁`:
`ṗ₁ = l₁ w₁ (cos q₁, sin q₁)`. -/
noncomputable def vel₁ (l₁ q₁ w₁ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (l₁ * w₁) • !₂[Real.cos q₁, Real.sin q₁]

/-- Velocity of the second point mass: `ṗ₂ = ṗ₁ + l₂ w₂ (cos q₂, sin q₂)`. -/
noncomputable def vel₂ (l₁ l₂ q₁ q₂ w₁ w₂ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  vel₁ l₁ q₁ w₁ + (l₂ * w₂) • !₂[Real.cos q₂, Real.sin q₂]

/-- Along an angle trajectory with `q₁' = w₁` and `q₂' = w₂` at `t`, the Cartesian positions have
the velocities `vel₁` and `vel₂` at `t`. -/
lemma hasDerivAt_pos {q₁ q₂ : ℝ → ℝ} {w₁ w₂ t : ℝ} (l₁ l₂ : ℝ) (h₁ : HasDerivAt q₁ w₁ t)
    (h₂ : HasDerivAt q₂ w₂ t) :
    HasDerivAt (fun s => pos₁ l₁ (q₁ s)) (vel₁ l₁ (q₁ t) w₁) t ∧
      HasDerivAt (fun s => pos₂ l₁ l₂ (q₁ s) (q₂ s)) (vel₂ l₁ l₂ (q₁ t) (q₂ t) w₁ w₂) t := by
  have key₁ : HasDerivAt ((fun s => (l₁ * Real.sin (q₁ s)) • !₂[(1 : ℝ), (0 : ℝ)]) +
      (fun s => ((-l₁) * Real.cos (q₁ s)) • !₂[(0 : ℝ), (1 : ℝ)]))
      ((l₁ * (Real.cos (q₁ t) * w₁)) • !₂[(1 : ℝ), (0 : ℝ)] +
        ((-l₁) * (-Real.sin (q₁ t) * w₁)) • !₂[(0 : ℝ), (1 : ℝ)]) t :=
    ((h₁.sin.const_mul l₁).smul_const _).add ((h₁.cos.const_mul (-l₁)).smul_const _)
  have funEq₁ : ∀ s, pos₁ l₁ (q₁ s) =
      (l₁ * Real.sin (q₁ s)) • !₂[(1 : ℝ), (0 : ℝ)] +
        ((-l₁) * Real.cos (q₁ s)) • !₂[(0 : ℝ), (1 : ℝ)] := by
    intro s
    ext i; fin_cases i <;> simp [pos₁]
  have valEq₁ : vel₁ l₁ (q₁ t) w₁ =
      (l₁ * (Real.cos (q₁ t) * w₁)) • !₂[(1 : ℝ), (0 : ℝ)] +
        ((-l₁) * (-Real.sin (q₁ t) * w₁)) • !₂[(0 : ℝ), (1 : ℝ)] := by
    ext i; fin_cases i <;> simp [vel₁] <;> ring
  have hpos₁ : HasDerivAt (fun s => pos₁ l₁ (q₁ s)) (vel₁ l₁ (q₁ t) w₁) t := by
    rw [valEq₁]
    apply key₁.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro s
    exact funEq₁ s
  have key₂ : HasDerivAt ((fun s => pos₁ l₁ (q₁ s)) +
      ((fun s => (l₂ * Real.sin (q₂ s)) • !₂[(1 : ℝ), (0 : ℝ)]) +
        (fun s => ((-l₂) * Real.cos (q₂ s)) • !₂[(0 : ℝ), (1 : ℝ)])))
      (vel₁ l₁ (q₁ t) w₁ +
        ((l₂ * (Real.cos (q₂ t) * w₂)) • !₂[(1 : ℝ), (0 : ℝ)] +
          ((-l₂) * (-Real.sin (q₂ t) * w₂)) • !₂[(0 : ℝ), (1 : ℝ)])) t :=
    hpos₁.add (((h₂.sin.const_mul l₂).smul_const _).add ((h₂.cos.const_mul (-l₂)).smul_const _))
  have funEq₂ : ∀ s, pos₂ l₁ l₂ (q₁ s) (q₂ s) =
      pos₁ l₁ (q₁ s) + ((l₂ * Real.sin (q₂ s)) • !₂[(1 : ℝ), (0 : ℝ)] +
        ((-l₂) * Real.cos (q₂ s)) • !₂[(0 : ℝ), (1 : ℝ)]) := by
    intro s
    ext i; fin_cases i <;> simp [pos₂, pos₁]
  have valEq₂ : vel₂ l₁ l₂ (q₁ t) (q₂ t) w₁ w₂ =
      vel₁ l₁ (q₁ t) w₁ + ((l₂ * (Real.cos (q₂ t) * w₂)) • !₂[(1 : ℝ), (0 : ℝ)] +
        ((-l₂) * (-Real.sin (q₂ t) * w₂)) • !₂[(0 : ℝ), (1 : ℝ)]) := by
    ext i; fin_cases i <;> simp [vel₂, vel₁] <;> ring
  refine ⟨hpos₁, ?_⟩
  rw [valEq₂]
  apply key₂.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro s
  exact funEq₂ s

/-! ## C. Kinetic energy, potential energy and the Lagrangian -/

/-- Kinetic energy of the two point masses, `m₁ ‖ṗ₁‖² / 2 + m₂ ‖ṗ₂‖² / 2`. -/
noncomputable def kineticEnergy (m₁ m₂ l₁ l₂ q₁ q₂ w₁ w₂ : ℝ) : ℝ :=
  m₁ * ‖vel₁ l₁ q₁ w₁‖ ^ 2 / 2 + m₂ * ‖vel₂ l₁ l₂ q₁ q₂ w₁ w₂‖ ^ 2 / 2

/-- Gravitational potential energy `g (m₁ y₁ + m₂ y₂)`, the heights `yᵢ` being the second
Cartesian coordinates and gravity `g` pointing along the downward vertical. -/
noncomputable def potentialEnergy (m₁ m₂ l₁ l₂ g q₁ q₂ : ℝ) : ℝ :=
  g * (m₁ * pos₁ l₁ q₁ 1 + m₂ * pos₂ l₁ l₂ q₁ q₂ 1)

/-- The Lagrangian `T - V` in the angle coordinates. -/
noncomputable def lagrangian (m₁ m₂ l₁ l₂ g q₁ q₂ w₁ w₂ : ℝ) : ℝ :=
  kineticEnergy m₁ m₂ l₁ l₂ q₁ q₂ w₁ w₂ - potentialEnergy m₁ m₂ l₁ l₂ g q₁ q₂

/-- The reduced mass matrix of the two-link model in the absolute angles. -/
noncomputable def massMatrix (m₁ m₂ l₁ l₂ q₁ q₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(m₁ + m₂) * l₁ ^ 2, m₂ * l₁ * l₂ * Real.cos (q₁ - q₂);
    m₂ * l₁ * l₂ * Real.cos (q₁ - q₂), m₂ * l₂ ^ 2]

private lemma norm_vel₁_sq (l₁ q₁ w₁ : ℝ) :
    ‖vel₁ l₁ q₁ w₁‖ ^ 2 = l₁ ^ 2 * w₁ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp [vel₁]
  have h := Real.cos_sq_add_sin_sq q₁
  linear_combination (l₁ * w₁) ^ 2 * h

private lemma norm_vel₂_sq (l₁ l₂ q₁ q₂ w₁ w₂ : ℝ) :
    ‖vel₂ l₁ l₂ q₁ q₂ w₁ w₂‖ ^ 2 =
      l₁ ^ 2 * w₁ ^ 2 + l₂ ^ 2 * w₂ ^ 2 +
        2 * l₁ * w₁ * l₂ * w₂ * Real.cos (q₁ - q₂) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp [vel₂, vel₁]
  have h1 := Real.cos_sq_add_sin_sq q₁
  have h2 := Real.cos_sq_add_sin_sq q₂
  have hc := Real.cos_sub q₁ q₂
  linear_combination (l₁ * w₁) ^ 2 * h1 + (l₂ * w₂) ^ 2 * h2 -
    (2 * l₁ * w₁ * l₂ * w₂) * hc

/-- The Cartesian kinetic energy is the quadratic form `wᵀ M(q) w / 2` of the reduced mass
matrix. -/
lemma kineticEnergy_eq_massMatrix (m₁ m₂ l₁ l₂ q₁ q₂ w₁ w₂ : ℝ) :
    kineticEnergy m₁ m₂ l₁ l₂ q₁ q₂ w₁ w₂ =
      (![w₁, w₂] ⬝ᵥ (massMatrix m₁ m₂ l₁ l₂ q₁ q₂ *ᵥ ![w₁, w₂])) / 2 := by
  simp only [kineticEnergy, norm_vel₁_sq, norm_vel₂_sq, Matrix.mulVec_apply_eq_sum, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp [massMatrix]
  ring

/-- If `q₁, q₂` have derivatives `w₁, w₂` at `t`, the kinetic energy of the actual Cartesian
velocities (the derivatives of the positions at `t`) is `wᵀ M(q(t)) w / 2`. -/
lemma kineticEnergy_actual {q₁ q₂ : ℝ → ℝ} {w₁ w₂ t : ℝ} (m₁ m₂ l₁ l₂ : ℝ)
    (h₁ : HasDerivAt q₁ w₁ t) (h₂ : HasDerivAt q₂ w₂ t) :
    m₁ * ‖deriv (fun s => pos₁ l₁ (q₁ s)) t‖ ^ 2 / 2 +
        m₂ * ‖deriv (fun s => pos₂ l₁ l₂ (q₁ s) (q₂ s)) t‖ ^ 2 / 2 =
      (![w₁, w₂] ⬝ᵥ (massMatrix m₁ m₂ l₁ l₂ (q₁ t) (q₂ t) *ᵥ ![w₁, w₂])) / 2 := by
  obtain ⟨h1', h2'⟩ := hasDerivAt_pos l₁ l₂ h₁ h₂
  rw [h1'.deriv, h2'.deriv]
  exact kineticEnergy_eq_massMatrix m₁ m₂ l₁ l₂ (q₁ t) (q₂ t) w₁ w₂

/-- The potential energy in the angles: `V = -(m₁ + m₂) g l₁ cos q₁ - m₂ g l₂ cos q₂`. -/
lemma potentialEnergy_eq (m₁ m₂ l₁ l₂ g q₁ q₂ : ℝ) :
    potentialEnergy m₁ m₂ l₁ l₂ g q₁ q₂ =
      -((m₁ + m₂) * g * l₁ * Real.cos q₁) - m₂ * g * l₂ * Real.cos q₂ := by
  simp [potentialEnergy, pos₁, pos₂]
  ring

/-- The Lagrangian of the coplanar double pendulum in the absolute angles. -/
lemma lagrangian_eq (m₁ m₂ l₁ l₂ g q₁ q₂ w₁ w₂ : ℝ) :
    lagrangian m₁ m₂ l₁ l₂ g q₁ q₂ w₁ w₂ =
      (m₁ + m₂) * l₁ ^ 2 * w₁ ^ 2 / 2 + m₂ * l₁ * l₂ * Real.cos (q₁ - q₂) * w₁ * w₂ +
        m₂ * l₂ ^ 2 * w₂ ^ 2 / 2 + (m₁ + m₂) * g * l₁ * Real.cos q₁ +
        m₂ * g * l₂ * Real.cos q₂ := by
  simp only [lagrangian, kineticEnergy_eq_massMatrix, potentialEnergy_eq,
    Matrix.mulVec_apply_eq_sum, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp [massMatrix]
  ring

/-! ## D. The reduced mass matrix is regular -/

/-- `det M = l₁² l₂² m₂ (m₁ + m₂ sin² (q₁ - q₂))`. -/
lemma massMatrix_det (m₁ m₂ l₁ l₂ q₁ q₂ : ℝ) :
    (massMatrix m₁ m₂ l₁ l₂ q₁ q₂).det =
      l₁ ^ 2 * l₂ ^ 2 * m₂ * (m₁ + m₂ * Real.sin (q₁ - q₂) ^ 2) := by
  simp [massMatrix, Matrix.det_fin_two]
  have h := Real.cos_sq_add_sin_sq (q₁ - q₂)
  linear_combination (-(m₂ * l₁ * l₂) ^ 2) * h

/-- For positive masses and lengths the determinant is positive in every configuration. -/
lemma massMatrix_det_pos {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) (q₁ q₂ : ℝ) : 0 < (massMatrix m₁ m₂ l₁ l₂ q₁ q₂).det := by
  rw [massMatrix_det]
  have hs : 0 ≤ Real.sin (q₁ - q₂) ^ 2 := sq_nonneg _
  exact mul_pos (mul_pos (mul_pos (sq_pos_of_ne_zero (ne_of_gt hl₁))
    (sq_pos_of_ne_zero (ne_of_gt hl₂))) hm₂)
    (add_pos_of_pos_of_nonneg hm₁ (mul_nonneg hm₂.le hs))

/-- Positive kinetic metric: for positive masses and lengths every nonzero angular velocity has
positive kinetic energy. -/
lemma kineticEnergy_pos {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) (q₁ q₂ : ℝ) {w₁ w₂ : ℝ} (hw : w₁ ≠ 0 ∨ w₂ ≠ 0) :
    0 < kineticEnergy m₁ m₂ l₁ l₂ q₁ q₂ w₁ w₂ := by
  by_cases hw₁ : w₁ = 0
  · subst hw₁
    rcases hw with h | h
    · exact absurd rfl h
    · have e2' : ‖vel₂ l₁ l₂ q₁ q₂ 0 w₂‖ ^ 2 = l₂ ^ 2 * w₂ ^ 2 := by
        rw [norm_vel₂_sq]
        ring
      have h1 : 0 ≤ m₁ * ‖vel₁ l₁ q₁ 0‖ ^ 2 / 2 := by positivity
      have h2 : 0 < m₂ * ‖vel₂ l₁ l₂ q₁ q₂ 0 w₂‖ ^ 2 / 2 := by
        rw [e2']
        have hw₂ := sq_pos_of_ne_zero h
        positivity
      simp only [kineticEnergy]
      linarith
  · have h1 : 0 < m₁ * ‖vel₁ l₁ q₁ w₁‖ ^ 2 / 2 := by
      rw [norm_vel₁_sq]
      have hw₁' := sq_pos_of_ne_zero hw₁
      positivity
    have h2 : 0 ≤ m₂ * ‖vel₂ l₁ l₂ q₁ q₂ w₁ w₂‖ ^ 2 / 2 := by positivity
    simp only [kineticEnergy]
    linarith

/-- Collinear links, `sin (q₁ - q₂) = 0` (stretched or folded), keep the determinant
`m₁ m₂ l₁² l₂²`, nonzero for nonzero masses and lengths: no rank loss for this open chain. -/
lemma massMatrix_det_of_collinear {q₁ q₂ : ℝ} (h : Real.sin (q₁ - q₂) = 0) (m₁ m₂ l₁ l₂ : ℝ) :
    (massMatrix m₁ m₂ l₁ l₂ q₁ q₂).det = m₁ * m₂ * l₁ ^ 2 * l₂ ^ 2 := by
  rw [massMatrix_det, h]
  ring

/-- A zero link length makes the reduced mass matrix singular. -/
lemma massMatrix_det_eq_zero_of_length_eq_zero {l₁ l₂ : ℝ} (h : l₁ = 0 ∨ l₂ = 0)
    (m₁ m₂ q₁ q₂ : ℝ) : (massMatrix m₁ m₂ l₁ l₂ q₁ q₂).det = 0 := by
  rw [massMatrix_det]
  rcases h with rfl | rfl <;> ring

/-! ## E. The rod constraints and their Jacobian -/

open scoped InnerProductSpace Topology

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The explicit angle-to-position map: the Cartesian configuration `(p₁, p₂)` of the two point
masses at the absolute link angles `q = (q₁, q₂)`. -/
noncomputable def posMap (l₁ l₂ : ℝ) (q : ℝ × ℝ) : ℝ² × ℝ² :=
  (pos₁ l₁ q.1, pos₂ l₁ l₂ q.1 q.2)

/-- The rod constraints on a Cartesian configuration `p = (p₁, p₂)`:
`g(p) = (‖p₁‖² - l₁², ‖p₂ - p₁‖² - l₂²)`; the rods, of lengths `|l₁|` and `|l₂|`, hold exactly where
`g(p) = 0`. -/
noncomputable def rodConstraint (l₁ l₂ : ℝ) (p : ℝ² × ℝ²) : ℝ × ℝ :=
  (‖p.1‖ ^ 2 - l₁ ^ 2, ‖p.2 - p.1‖ ^ 2 - l₂ ^ 2)

/-- The constraint Jacobian at `p = (p₁, p₂)`, the derivative of `rodConstraint`
(`hasFDerivAt_rodConstraint`): `(v₁, v₂) ↦ (2 ⟪p₁, v₁⟫, 2 ⟪p₂ - p₁, v₂ - v₁⟫)`. Its two rows pair
a velocity with the constraint gradients `(2 p₁, 0)` and `(-2 (p₂ - p₁), 2 (p₂ - p₁))`. -/
noncomputable def rodJacobian (p : ℝ² × ℝ²) : ℝ² × ℝ² →L[ℝ] ℝ × ℝ :=
  ((2 : ℝ) • (innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ ℝ² ℝ²)).prod
    ((2 : ℝ) • (innerSL ℝ (p.2 - p.1)).comp
      (ContinuousLinearMap.snd ℝ ℝ² ℝ² - ContinuousLinearMap.fst ℝ ℝ² ℝ²))

/-- The angle derivative of the position map at `q`, the derivative of `posMap`
(`hasFDerivAt_posMap`): angular velocities `w = (w₁, w₂)` go to the Cartesian velocities
`(vel₁ l₁ q₁ w₁, vel₂ l₁ l₂ q₁ q₂ w₁ w₂)` (`angleJacobian_apply`). -/
noncomputable def angleJacobian (l₁ l₂ : ℝ) (q : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ² × ℝ² :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (l₁ • !₂[Real.cos q.1, Real.sin q.1])).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (l₁ • !₂[Real.cos q.1, Real.sin q.1]) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (l₂ • !₂[Real.cos q.2, Real.sin q.2]))

private lemma inner_two (u v : ℝ²) : ⟪u, v⟫_ℝ = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

private lemma normsq_two (u : ℝ²) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

private lemma ext_two {u v : ℝ²} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i; fin_cases i <;> simp [h0, h1]

private lemma posMap_coords (l₁ l₂ : ℝ) (q : ℝ × ℝ) :
    (posMap l₁ l₂ q).1 0 = l₁ * Real.sin q.1 ∧ (posMap l₁ l₂ q).1 1 = -(l₁ * Real.cos q.1) ∧
      (posMap l₁ l₂ q).2 0 = l₁ * Real.sin q.1 + l₂ * Real.sin q.2 ∧
      (posMap l₁ l₂ q).2 1 = -(l₁ * Real.cos q.1) - l₂ * Real.cos q.2 := by
  refine ⟨by simp [posMap, pos₁], by simp [posMap, pos₁], by simp [posMap, pos₁, pos₂], ?_⟩
  simp [posMap, pos₁, pos₂]; ring

private lemma angleJacobian_coords (l₁ l₂ : ℝ) (q w : ℝ × ℝ) :
    (angleJacobian l₁ l₂ q w).1 0 = l₁ * w.1 * Real.cos q.1 ∧
      (angleJacobian l₁ l₂ q w).1 1 = l₁ * w.1 * Real.sin q.1 ∧
      (angleJacobian l₁ l₂ q w).2 0 = l₁ * w.1 * Real.cos q.1 + l₂ * w.2 * Real.cos q.2 ∧
      (angleJacobian l₁ l₂ q w).2 1 = l₁ * w.1 * Real.sin q.1 + l₂ * w.2 * Real.sin q.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [angleJacobian] <;> ring

private lemma rodJacobian_coords (p v : ℝ² × ℝ²) :
    rodJacobian p v = (2 * (p.1 0 * v.1 0 + p.1 1 * v.1 1),
      2 * ((p.2 0 - p.1 0) * (v.2 0 - v.1 0) + (p.2 1 - p.1 1) * (v.2 1 - v.1 1))) := by
  have h : rodJacobian p v = (2 * ⟪p.1, v.1⟫_ℝ, 2 * ⟪p.2 - p.1, v.2 - v.1⟫_ℝ) := by
    ext <;> simp [rodJacobian, inner_sub_left, inner_sub_right]
  rw [h, inner_two, inner_two]
  simp

private lemma rodJacobian_posMap_angleJacobian (l₁ l₂ : ℝ) (q w : ℝ × ℝ) :
    rodJacobian (posMap l₁ l₂ q) (angleJacobian l₁ l₂ q w) = 0 := by
  obtain ⟨a0, a1, a2, a3⟩ := posMap_coords l₁ l₂ q
  obtain ⟨b0, b1, b2, b3⟩ := angleJacobian_coords l₁ l₂ q w
  rw [rodJacobian_coords, a0, a1, a2, a3, b0, b1, b2, b3]
  ext <;> simp <;> ring

/-- The explicit angle-to-position map satisfies both rod constraints, for any real lengths. -/
lemma rodConstraint_posMap (l₁ l₂ : ℝ) (q : ℝ × ℝ) : rodConstraint l₁ l₂ (posMap l₁ l₂ q) = 0 := by
  obtain ⟨a0, a1, a2, a3⟩ := posMap_coords l₁ l₂ q
  have hs1 := Real.sin_sq_add_cos_sq q.1
  have hs2 := Real.sin_sq_add_cos_sq q.2
  simp only [rodConstraint]
  rw [normsq_two, normsq_two]
  simp only [PiLp.sub_apply, a0, a1, a2, a3]
  ext
  · simp only [Prod.fst_zero]; linear_combination l₁ ^ 2 * hs1
  · simp only [Prod.snd_zero]; linear_combination l₂ ^ 2 * hs2

/-- The constraint Jacobian in components. -/
lemma rodJacobian_apply (p v : ℝ² × ℝ²) :
    rodJacobian p v = (2 * ⟪p.1, v.1⟫_ℝ, 2 * ⟪p.2 - p.1, v.2 - v.1⟫_ℝ) := by
  ext <;> simp [rodJacobian, inner_sub_left, inner_sub_right]

/-- `rodJacobian p` is the derivative of the rod constraint map at `p`. -/
lemma hasFDerivAt_rodConstraint (l₁ l₂ : ℝ) (p : ℝ² × ℝ²) :
    HasFDerivAt (rodConstraint l₁ l₂) (rodJacobian p) p := by
  have h1 := (hasFDerivAt_fst (p := p) (𝕜 := ℝ)).norm_sq
  have h2 := ((hasFDerivAt_snd (p := p) (𝕜 := ℝ)).sub (hasFDerivAt_fst (p := p) (𝕜 := ℝ))).norm_sq
  have h := ((h1.sub_const (l₁ ^ 2)).prodMk (h2.sub_const (l₂ ^ 2))).congr_fderiv
    (g' := rodJacobian p) (by
      refine ContinuousLinearMap.ext fun v => ?_
      refine Prod.ext ?_ ?_ <;> simp [rodJacobian, nsmul_eq_mul])
  exact h

/-- The angle derivative sends angular velocities to the Cartesian velocities `(vel₁, vel₂)` of the
two masses. -/
lemma angleJacobian_apply (l₁ l₂ : ℝ) (q w : ℝ × ℝ) :
    angleJacobian l₁ l₂ q w = (vel₁ l₁ q.1 w.1, vel₂ l₁ l₂ q.1 q.2 w.1 w.2) := by
  simp [angleJacobian, vel₁, vel₂, smul_smul, mul_comm]

/-- `angleJacobian l₁ l₂ q` is the derivative of the angle-to-position map at `q`. -/
lemma hasFDerivAt_posMap (l₁ l₂ : ℝ) (q : ℝ × ℝ) :
    HasFDerivAt (posMap l₁ l₂) (angleJacobian l₁ l₂ q) q := by
  have e₁ : ∀ a b : ℝ, (!₂[a, b] : ℝ²) = a • !₂[(1 : ℝ), 0] + b • !₂[(0 : ℝ), 1] := by
    intro a b; ext i; fin_cases i <;> simp
  have hfst : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) q :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
    hasFDerivAt_snd
  have hs1 := (Real.hasDerivAt_sin q.1).comp_hasFDerivAt q hfst
  have hc1 := (Real.hasDerivAt_cos q.1).comp_hasFDerivAt q hfst
  have hs2 := (Real.hasDerivAt_sin q.2).comp_hasFDerivAt q hsnd
  have hc2 := (Real.hasDerivAt_cos q.2).comp_hasFDerivAt q hsnd
  have hp1 : HasFDerivAt (fun q : ℝ × ℝ => pos₁ l₁ q.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (l₁ • !₂[Real.cos q.1, Real.sin q.1])) q := by
    have h := ((hs1.const_mul l₁).smul_const !₂[(1 : ℝ), 0]).add
      ((hc1.const_mul (-l₁)).smul_const !₂[(0 : ℝ), 1])
    convert h using 1
    · funext x; simp only [pos₁, Function.comp]; ext i; fin_cases i <;> simp
    · refine ContinuousLinearMap.ext fun w => ext_two ?_ ?_ <;> simp <;> ring
  have hp2 : HasFDerivAt (fun q : ℝ × ℝ => l₂ • !₂[Real.sin q.2, -Real.cos q.2])
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (l₂ • !₂[Real.cos q.2, Real.sin q.2])) q := by
    have h := ((hs2.const_mul l₂).smul_const !₂[(1 : ℝ), 0]).add
      ((hc2.const_mul (-l₂)).smul_const !₂[(0 : ℝ), 1])
    convert h using 1
    · funext x; simp only [Function.comp]; ext i; fin_cases i <;> simp
    · refine ContinuousLinearMap.ext fun w => ext_two ?_ ?_ <;> simp <;> ring
  exact hp1.prodMk (hp1.add hp2)

/-- Rank two at every configuration of the open chain, collinear links included: for positive
lengths the constraint Jacobian at `posMap q`, whose rows are the two constraint gradients, has a
two-dimensional range. -/
lemma rodJacobian_rank_two {l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (q : ℝ × ℝ) :
    Module.finrank ℝ (LinearMap.range (rodJacobian (posMap l₁ l₂ q)).toLinearMap) = 2 := by
  have hn : ‖(posMap l₁ l₂ q).1‖ ^ 2 = l₁ ^ 2 ∧
      ‖(posMap l₁ l₂ q).2 - (posMap l₁ l₂ q).1‖ ^ 2 = l₂ ^ 2 := by
    have h := rodConstraint_posMap l₁ l₂ q
    simp only [rodConstraint, Prod.mk_eq_zero, sub_eq_zero] at h
    exact h
  have hl₁' : l₁ ≠ 0 := hl₁.ne'
  have hl₂' : l₂ ≠ 0 := hl₂.ne'
  have hsurj : Function.Surjective (rodJacobian (posMap l₁ l₂ q)) := by
    intro c
    refine ⟨((c.1 / (2 * l₁ ^ 2)) • (posMap l₁ l₂ q).1,
      (c.1 / (2 * l₁ ^ 2)) • (posMap l₁ l₂ q).1 +
        (c.2 / (2 * l₂ ^ 2)) • ((posMap l₁ l₂ q).2 - (posMap l₁ l₂ q).1)), ?_⟩
    rw [rodJacobian_apply]
    simp only [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hn.1, hn.2]
    ext
    · simp only; field_simp
    · simp only; field_simp
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod, Module.finrank_self]

/-! ## F. The tangent space -/

/-- For positive lengths the angle derivative is injective. -/
lemma ker_angleJacobian {l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (q : ℝ × ℝ) :
    LinearMap.ker (angleJacobian l₁ l₂ q).toLinearMap = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro w hw
  have hw' : angleJacobian l₁ l₂ q w = 0 := hw
  obtain ⟨b0, b1, b2, b3⟩ := angleJacobian_coords l₁ l₂ q w
  have h0 : (angleJacobian l₁ l₂ q w).1 0 = 0 := by rw [hw']; rfl
  have h1 : (angleJacobian l₁ l₂ q w).1 1 = 0 := by rw [hw']; rfl
  have h2 : (angleJacobian l₁ l₂ q w).2 0 = 0 := by rw [hw']; rfl
  have h3 : (angleJacobian l₁ l₂ q w).2 1 = 0 := by rw [hw']; rfl
  rw [b0] at h0; rw [b1] at h1; rw [b2] at h2; rw [b3] at h3
  have hc1 := Real.sin_sq_add_cos_sq q.1
  have hc2 := Real.sin_sq_add_cos_sq q.2
  have hw1 : l₁ * w.1 = 0 := by
    linear_combination Real.cos q.1 * h0 + Real.sin q.1 * h1 - l₁ * w.1 * hc1
  have hw2 : l₂ * w.2 = 0 := by
    linear_combination Real.cos q.2 * h2 + Real.sin q.2 * h3 - l₂ * w.2 * hc2 -
      Real.cos q.2 * Real.cos q.1 * hw1 - Real.sin q.2 * Real.sin q.1 * hw1
  have e1 : w.1 = 0 := (mul_eq_zero.mp hw1).resolve_left hl₁.ne'
  have e2 : w.2 = 0 := (mul_eq_zero.mp hw2).resolve_left hl₂.ne'
  exact Prod.ext e1 e2

/-- For positive lengths the range of the angle derivative is the kernel of the constraint
Jacobian at `posMap q`; with `ker_angleJacobian`, the angle derivative identifies the angular
velocities with that kernel. -/
lemma range_angleJacobian {l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (q : ℝ × ℝ) :
    LinearMap.range (angleJacobian l₁ l₂ q).toLinearMap =
      LinearMap.ker (rodJacobian (posMap l₁ l₂ q)).toLinearMap := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact rodJacobian_posMap_angleJacobian l₁ l₂ q w
  · intro hv
    have hv' : rodJacobian (posMap l₁ l₂ q) v = 0 := hv
    obtain ⟨a0, a1, a2, a3⟩ := posMap_coords l₁ l₂ q
    rw [rodJacobian_coords, a0, a1, a2, a3, Prod.mk_eq_zero] at hv'
    obtain ⟨k1, k2⟩ := hv'
    have hc1 := Real.sin_sq_add_cos_sq q.1
    have hc2 := Real.sin_sq_add_cos_sq q.2
    have hl₁' : l₁ ≠ 0 := hl₁.ne'
    have hl₂' : l₂ ≠ 0 := hl₂.ne'
    have k1' : Real.sin q.1 * v.1 0 - Real.cos q.1 * v.1 1 = 0 := by
      have : l₁ * (Real.sin q.1 * v.1 0 - Real.cos q.1 * v.1 1) = 0 := by
        linear_combination k1 / 2
      exact (mul_eq_zero.mp this).resolve_left hl₁'
    have k2' : Real.sin q.2 * (v.2 0 - v.1 0) - Real.cos q.2 * (v.2 1 - v.1 1) = 0 := by
      have : l₂ * (Real.sin q.2 * (v.2 0 - v.1 0) - Real.cos q.2 * (v.2 1 - v.1 1)) = 0 := by
        linear_combination k2 / 2
      exact (mul_eq_zero.mp this).resolve_left hl₂'
    set μ₁ := v.1 0 * Real.cos q.1 + v.1 1 * Real.sin q.1 with hμ₁
    set μ₂ := (v.2 0 - v.1 0) * Real.cos q.2 + (v.2 1 - v.1 1) * Real.sin q.2 with hμ₂
    refine ⟨(μ₁ / l₁, μ₂ / l₂), ?_⟩
    obtain ⟨b0, b1, b2, b3⟩ := angleJacobian_coords l₁ l₂ q (μ₁ / l₁, μ₂ / l₂)
    have f1 : l₁ * (μ₁ / l₁) = μ₁ := by field_simp
    have f2 : l₂ * (μ₂ / l₂) = μ₂ := by field_simp
    simp only [f1, f2] at b0 b1 b2 b3
    change angleJacobian l₁ l₂ q (μ₁ / l₁, μ₂ / l₂) = v
    refine Prod.ext (ext_two ?_ ?_) (ext_two ?_ ?_)
    · rw [b0, hμ₁]
      linear_combination (-Real.sin q.1) * k1' + v.1 0 * hc1
    · rw [b1, hμ₁]
      linear_combination Real.cos q.1 * k1' + v.1 1 * hc1
    · rw [b2, hμ₁, hμ₂]
      linear_combination (-Real.sin q.1) * k1' + v.1 0 * hc1 + (-Real.sin q.2) * k2' +
        (v.2 0 - v.1 0) * hc2
    · rw [b3, hμ₁, hμ₂]
      linear_combination Real.cos q.1 * k1' + v.1 1 * hc1 + Real.cos q.2 * k2' +
        (v.2 1 - v.1 1) * hc2

/-- Velocities of constrained motions are in the kernel: a Cartesian curve that satisfies both rod
constraints near `t` and has velocity `v` at `t` satisfies `Dg(c t) v = 0`. -/
lemma rodJacobian_velocity_eq_zero {l₁ l₂ : ℝ} {c : ℝ → ℝ² × ℝ²} {v : ℝ² × ℝ²} {t : ℝ}
    (hc : ∀ᶠ s in 𝓝 t, rodConstraint l₁ l₂ (c s) = 0) (hv : HasDerivAt c v t) :
    rodJacobian (c t) v = 0 := by
  have h1 : HasDerivAt (fun s => rodConstraint l₁ l₂ (c s)) (rodJacobian (c t) v) t :=
    (hasFDerivAt_rodConstraint l₁ l₂ (c t)).comp_hasDerivAt t hv
  have h2 : HasDerivAt (fun s => rodConstraint l₁ l₂ (c s)) 0 t :=
    (hasDerivAt_const t (0 : ℝ × ℝ)).congr_of_eventuallyEq hc
  exact h1.unique h2

/-- For positive lengths, every kernel vector at `posMap q` is the velocity at `s = 0` of the
explicit constrained curve `s ↦ posMap (q + s w)`, for exactly one angular velocity `w`. -/
lemma existsUnique_hasDerivAt_posMap {l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (q : ℝ × ℝ)
    {v : ℝ² × ℝ²} (hv : rodJacobian (posMap l₁ l₂ q) v = 0) :
    ∃! w : ℝ × ℝ, HasDerivAt (fun s : ℝ => posMap l₁ l₂ (q + s • w)) v 0 := by
  have hmem : v ∈ LinearMap.range (angleJacobian l₁ l₂ q).toLinearMap := by
    rw [range_angleJacobian hl₁ hl₂ q]; exact hv
  obtain ⟨w, hw⟩ := hmem
  have hw' : angleJacobian l₁ l₂ q w = v := hw
  have hcurve : ∀ w' : ℝ × ℝ,
      HasDerivAt (fun s : ℝ => posMap l₁ l₂ (q + s • w')) (angleJacobian l₁ l₂ q w') 0 := by
    intro w'
    have hline : HasDerivAt (fun s : ℝ => q + s • w') w' 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w').const_add q
    have h := (hasFDerivAt_posMap l₁ l₂ (q + (0 : ℝ) • w')).comp_hasDerivAt (0 : ℝ) hline
    simp only [zero_smul, add_zero] at h
    exact h
  refine ⟨w, ?_, ?_⟩
  · have := hcurve w
    rwa [hw'] at this
  · intro w' hw''
    have e : angleJacobian l₁ l₂ q w' = angleJacobian l₁ l₂ q w :=
      ((hcurve w').unique hw'').trans hw'.symm
    exact (LinearMap.ker_eq_bot.mp (ker_angleJacobian hl₁ hl₂ q)) e

/-! ## G. Rod reactions and virtual work -/

/-- Rod-normal reactions with multipliers `c₁, c₂` at `p = (p₁, p₂)`: the first rod acts on the
first mass along `p₁`; the second rod acts on the second mass along `p₂ - p₁` and on the first mass
with the opposite force. This is `(c₁ ∇g₁ + c₂ ∇g₂) / 2`; at a configuration with `‖p₁‖ = l₁ > 0`
and `‖p₂ - p₁‖ = l₂ > 0`, a tension `T₁ > 0` in the first rod is `c₁ = -T₁ / l₁`, and a tension
`T₂ > 0` in the second is `c₂ = -T₂ / l₂`. -/
noncomputable def rodReaction (c₁ c₂ : ℝ) (p : ℝ² × ℝ²) : ℝ² × ℝ² :=
  (c₁ • p.1 - c₂ • (p.2 - p.1), c₂ • (p.2 - p.1))

/-- The virtual work `⟪F₁, v₁⟫ + ⟪F₂, v₂⟫` of the forces `F = (F₁, F₂)` on the two masses along the
virtual velocity `v = (v₁, v₂)`. -/
noncomputable def virtualWork (F v : ℝ² × ℝ²) : ℝ :=
  ⟪F.1, v.1⟫_ℝ + ⟪F.2, v.2⟫_ℝ

/-- Virtual-work annihilation: rod-normal reactions do no virtual work along any kernel vector of
the constraint Jacobian. -/
lemma virtualWork_rodReaction_eq_zero (c₁ c₂ : ℝ) {p v : ℝ² × ℝ²} (hv : rodJacobian p v = 0) :
    virtualWork (rodReaction c₁ c₂ p) v = 0 := by
  rw [rodJacobian_apply, Prod.mk_eq_zero] at hv
  obtain ⟨h1, h2⟩ := hv
  simp only [virtualWork, rodReaction, inner_sub_left, real_inner_smul_left]
  simp only [inner_sub_left, inner_sub_right] at h2
  linear_combination (c₁ / 2) * h1 + (c₂ / 2) * h2

/-- Rod reactions do no work along any motion of the chain: at `posMap q` they annihilate every
velocity `angleJacobian q w`, for any real lengths. -/
lemma virtualWork_rodReaction_angleJacobian (c₁ c₂ l₁ l₂ : ℝ) (q w : ℝ × ℝ) :
    virtualWork (rodReaction c₁ c₂ (posMap l₁ l₂ q)) (angleJacobian l₁ l₂ q w) = 0 := by
  exact virtualWork_rodReaction_eq_zero c₁ c₂ (rodJacobian_posMap_angleJacobian l₁ l₂ q w)

/-- The converse, for positive lengths: a force pair that does no virtual work along the kernel of
the constraint Jacobian at `posMap q` is a rod-normal reaction, with unique multipliers. -/
lemma existsUnique_rodReaction {l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (q : ℝ × ℝ)
    {F : ℝ² × ℝ²} (hF : ∀ v, rodJacobian (posMap l₁ l₂ q) v = 0 → virtualWork F v = 0) :
    ∃! c : ℝ × ℝ, F = rodReaction c.1 c.2 (posMap l₁ l₂ q) := by
  obtain ⟨a0, a1, a2, a3⟩ := posMap_coords l₁ l₂ q
  have hc1 := Real.sin_sq_add_cos_sq q.1
  have hc2 := Real.sin_sq_add_cos_sq q.2
  have hl₁' : l₁ ≠ 0 := hl₁.ne'
  have hl₂' : l₂ ≠ 0 := hl₂.ne'
  have t1 := hF ((0 : ℝ²), !₂[Real.cos q.2, Real.sin q.2]) (by
    rw [rodJacobian_coords, a0, a1, a2, a3]; ext <;> simp; ring)
  have t2 := hF (!₂[Real.cos q.1, Real.sin q.1], !₂[Real.cos q.1, Real.sin q.1]) (by
    rw [rodJacobian_coords, a0, a1, a2, a3]; ext <;> simp; ring)
  simp only [virtualWork, inner_two] at t1 t2
  simp only [Fin.isValue, PiLp.zero_apply, mul_zero, add_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_add] at t1 t2
  set s₁ := Real.sin q.1 with hs₁
  set k₁ := Real.cos q.1 with hk₁
  set s₂ := Real.sin q.2 with hs₂
  set k₂ := Real.cos q.2 with hk₂
  set C₂ := (F.2 0 * s₂ - F.2 1 * k₂) / l₂ with hC₂def
  set C₁ := ((F.1 0 + F.2 0) * s₁ - (F.1 1 + F.2 1) * k₁) / l₁ with hC₁def
  have hC₂ : C₂ * l₂ = F.2 0 * s₂ - F.2 1 * k₂ := by rw [hC₂def]; field_simp
  have hC₁ : C₁ * l₁ = (F.1 0 + F.2 0) * s₁ - (F.1 1 + F.2 1) * k₁ := by rw [hC₁def]; field_simp
  refine ⟨(C₁, C₂), ?_, ?_⟩
  · change F = rodReaction C₁ C₂ (posMap l₁ l₂ q)
    refine Prod.ext (ext_two ?_ ?_) (ext_two ?_ ?_)
    · simp only [rodReaction, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, a0, a2]
      linear_combination (-s₁) * hC₁ + s₂ * hC₂ + k₁ * t2 - (F.1 0 + F.2 0) * hc1 -
        k₂ * t1 + F.2 0 * hc2
    · simp only [rodReaction, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, a1, a3]
      linear_combination k₁ * hC₁ - k₂ * hC₂ + s₁ * t2 - (F.1 1 + F.2 1) * hc1 -
        s₂ * t1 + F.2 1 * hc2
    · simp only [rodReaction, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, a0, a2]
      linear_combination (-s₂) * hC₂ + k₂ * t1 - F.2 0 * hc2
    · simp only [rodReaction, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, a1, a3]
      linear_combination k₂ * hC₂ + s₂ * t1 - F.2 1 * hc2
  · rintro ⟨d₁, d₂⟩ hd
    have hd' : F = rodReaction d₁ d₂ (posMap l₁ l₂ q) := hd
    have u0 := congrArg (fun G : ℝ² × ℝ² => G.1 0) hd'
    have u1 := congrArg (fun G : ℝ² × ℝ² => G.1 1) hd'
    have u2 := congrArg (fun G : ℝ² × ℝ² => G.2 0) hd'
    have u3 := congrArg (fun G : ℝ² × ℝ² => G.2 1) hd'
    simp only [rodReaction, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, a0, a1, a2, a3]
      at u0 u1 u2 u3
    have e2 : d₂ = C₂ := by
      have h : l₂ * (d₂ - C₂) = 0 := by
        linear_combination (-1 : ℝ) * hC₂ - s₂ * u2 + k₂ * u3 - d₂ * l₂ * hc2
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hl₂')
    have e1 : d₁ = C₁ := by
      have h : l₁ * (d₁ - C₁) = 0 := by
        linear_combination (-1 : ℝ) * hC₁ - s₁ * (u0 + u2) + k₁ * (u1 + u3) - d₁ * l₁ * hc1
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hl₁')
    rw [e1, e2]

/-! ## H. The reduced Euler-Lagrange equation -/

open scoped ContDiff Time
open ClassicalMechanics (eulerLagrangeOp)

/-- The two-link Lagrangian in the carrier type of `ClassicalMechanics.eulerLagrangeOp`:
time-independent, with the angles `q = (q₁, q₂)` and the angular velocities `v = (w₁, w₂)` as
vectors of the Euclidean plane; in coordinates it is `lagrangian`. -/
noncomputable def angleLagrangian (m₁ m₂ l₁ l₂ g : ℝ) (_ : Time) (q v : ℝ²) : ℝ :=
  lagrangian m₁ m₂ l₁ l₂ g (q 0) (q 1) (v 0) (v 1)

/-- The generalized force `f(q, w)` of the reduced equation `M(q) q̈ = f(q, q̇)`: the gravity
torques and the velocity-quadratic terms, `f₁ = -m₂ l₁ l₂ sin (q₁ - q₂) w₂² - (m₁ + m₂) g l₁ sin q₁`
and `f₂ = m₂ l₁ l₂ sin (q₁ - q₂) w₁² - m₂ g l₂ sin q₂`. -/
noncomputable def generalizedForce (m₁ m₂ l₁ l₂ g : ℝ) (q w : ℝ²) : ℝ² :=
  !₂[-(m₂ * l₁ * l₂ * Real.sin (q 0 - q 1) * w 1 ^ 2) - (m₁ + m₂) * g * l₁ * Real.sin (q 0),
    m₂ * l₁ * l₂ * Real.sin (q 0 - q 1) * w 0 ^ 2 - m₂ * g * l₂ * Real.sin (q 1)]

/-- The reduced Euler-Lagrange acceleration `M(q)⁻¹ f(q, w)`, by Cramer's rule with the determinant
`l₁² l₂² m₂ (m₁ + m₂ sin² (q₁ - q₂))` of the reduced mass matrix. With the convention `x / 0 = 0`,
both components are `0` where that determinant vanishes, for example when `m₂ = 0` or a length
is `0`. -/
noncomputable def reducedAccel (m₁ m₂ l₁ l₂ g : ℝ) (q w : ℝ²) : ℝ² :=
  !₂[(m₂ * l₂ ^ 2 * generalizedForce m₁ m₂ l₁ l₂ g q w 0 -
        m₂ * l₁ * l₂ * Real.cos (q 0 - q 1) * generalizedForce m₁ m₂ l₁ l₂ g q w 1) /
      (l₁ ^ 2 * l₂ ^ 2 * m₂ * (m₁ + m₂ * Real.sin (q 0 - q 1) ^ 2)),
    ((m₁ + m₂) * l₁ ^ 2 * generalizedForce m₁ m₂ l₁ l₂ g q w 1 -
        m₂ * l₁ * l₂ * Real.cos (q 0 - q 1) * generalizedForce m₁ m₂ l₁ l₂ g q w 0) /
      (l₁ ^ 2 * l₂ ^ 2 * m₂ * (m₁ + m₂ * Real.sin (q 0 - q 1) ^ 2))]

private lemma det_pos' {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) (x : ℝ) : 0 < l₁ ^ 2 * l₂ ^ 2 * m₂ * (m₁ + m₂ * Real.sin x ^ 2) := by
  positivity

private lemma massMatrix_mulVec_reducedAccel {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (g : ℝ) (q w : ℝ²) :
    massMatrix m₁ m₂ l₁ l₂ (q 0) (q 1) *ᵥ (reducedAccel m₁ m₂ l₁ l₂ g q w).ofLp =
      (generalizedForce m₁ m₂ l₁ l₂ g q w).ofLp := by
  have hD := (det_pos' hm₁ hm₂ hl₁ hl₂ (q 0 - q 1)).ne'
  have h := Real.sin_sq_add_cos_sq (q 0 - q 1)
  ext i
  fin_cases i
  · simp [massMatrix, reducedAccel, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    linear_combination (-(m₂ * l₂ * (generalizedForce m₁ m₂ l₁ l₂ g q w).ofLp 0)) * h
  · simp [massMatrix, reducedAccel, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    linear_combination (-(m₂ * l₁ * (generalizedForce m₁ m₂ l₁ l₂ g q w).ofLp 1)) * h

/-- For positive masses and lengths the reduced acceleration is `M(q)⁻¹ f(q, w)` for the invertible
reduced mass matrix. -/
lemma reducedAccel_eq_inv_mulVec {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) (g : ℝ) (q w : ℝ²) :
    (reducedAccel m₁ m₂ l₁ l₂ g q w).ofLp =
      (massMatrix m₁ m₂ l₁ l₂ (q 0) (q 1))⁻¹ *ᵥ (generalizedForce m₁ m₂ l₁ l₂ g q w).ofLp := by
  have hdet : IsUnit (massMatrix m₁ m₂ l₁ l₂ (q 0) (q 1)).det :=
    (massMatrix_det_pos hm₁ hm₂ hl₁ hl₂ (q 0) (q 1)).ne'.isUnit
  rw [← massMatrix_mulVec_reducedAccel hm₁ hm₂ hl₁ hl₂ g q w, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- `M a = f` determines `a` as the reduced acceleration. -/
private lemma mulVec_eq_iff_eq_reducedAccel {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (g : ℝ) (q w a : ℝ²) :
    massMatrix m₁ m₂ l₁ l₂ (q 0) (q 1) *ᵥ a.ofLp = (generalizedForce m₁ m₂ l₁ l₂ g q w).ofLp ↔
      a = reducedAccel m₁ m₂ l₁ l₂ g q w := by
  constructor
  · intro h
    have hdet : IsUnit (massMatrix m₁ m₂ l₁ l₂ (q 0) (q 1)).det :=
      (massMatrix_det_pos hm₁ hm₂ hl₁ hl₂ (q 0) (q 1)).ne'.isUnit
    apply WithLp.ofLp_injective
    rw [reducedAccel_eq_inv_mulVec hm₁ hm₂ hl₁ hl₂, ← h, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  · rintro rfl
    exact massMatrix_mulVec_reducedAccel hm₁ hm₂ hl₁ hl₂ g q w

private lemma gradient_eq_two (f : ℝ² → ℝ) (x : ℝ²) :
    gradient f x = !₂[fderiv ℝ f x (EuclideanSpace.single 0 1),
      fderiv ℝ f x (EuclideanSpace.single 1 1)] := by
  have key : ∀ i : Fin 2, gradient f x i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
    intro i
    rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
    simp
  ext i
  fin_cases i <;> simp [key]

private lemma hasFDerivAt_coord (i : Fin 2) (x : ℝ²) :
    HasFDerivAt (fun y : ℝ² => y i) (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ) x :=
  (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).hasFDerivAt

/-- The gradient of the two-link Lagrangian in the angles. -/
private lemma gradient_angleLagrangian_left (m₁ m₂ l₁ l₂ g : ℝ) (t : Time) (x v : ℝ²) :
    gradient (fun y => angleLagrangian m₁ m₂ l₁ l₂ g t y v) x =
      !₂[-(m₂ * l₁ * l₂ * Real.sin (x 0 - x 1) * v 0 * v 1) - (m₁ + m₂) * g * l₁ * Real.sin (x 0),
        m₂ * l₁ * l₂ * Real.sin (x 0 - x 1) * v 0 * v 1 - m₂ * g * l₂ * Real.sin (x 1)] := by
  have h0 := hasFDerivAt_coord 0 x
  have h1 := hasFDerivAt_coord 1 x
  have hF := (((((hasFDerivAt_const ((m₁ + m₂) * l₁ ^ 2 * v 0 ^ 2 / 2) x).add
    ((((h0.sub h1).cos.const_mul (m₂ * l₁ * l₂)).mul_const (v 0)).mul_const (v 1))).add
    (hasFDerivAt_const (m₂ * l₂ ^ 2 * v 1 ^ 2 / 2) x)).add
    (h0.cos.const_mul ((m₁ + m₂) * g * l₁))).add (h1.cos.const_mul (m₂ * g * l₂)))
  have hL : HasFDerivAt (fun y => angleLagrangian m₁ m₂ l₁ l₂ g t y v) _ x :=
    hF.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by
      simp only [angleLagrangian, lagrangian_eq, Pi.add_apply, Pi.sub_apply])
  rw [gradient_eq_two, hL.fderiv]
  ext i
  fin_cases i
  · simp; ring
  · simp; ring

/-- The gradient of the two-link Lagrangian in the angular velocities: `M(q) v`. -/
private lemma gradient_angleLagrangian_right (m₁ m₂ l₁ l₂ g : ℝ) (t : Time) (x v : ℝ²) :
    gradient (angleLagrangian m₁ m₂ l₁ l₂ g t x) v =
      !₂[(m₁ + m₂) * l₁ ^ 2 * v 0 + m₂ * l₁ * l₂ * Real.cos (x 0 - x 1) * v 1,
        m₂ * l₁ * l₂ * Real.cos (x 0 - x 1) * v 0 + m₂ * l₂ ^ 2 * v 1] := by
  have h0 := hasFDerivAt_coord 0 v
  have h1 := hasFDerivAt_coord 1 v
  have hF := ((((h0.pow 2).const_mul ((m₁ + m₂) * l₁ ^ 2)).mul_const (1 / 2)).add
    ((h0.const_mul (m₂ * l₁ * l₂ * Real.cos (x 0 - x 1))).mul h1)).add
    (((h1.pow 2).const_mul (m₂ * l₂ ^ 2)).mul_const (1 / 2)) |>.add_const
    ((m₁ + m₂) * g * l₁ * Real.cos (x 0) + m₂ * g * l₂ * Real.cos (x 1))
  have hL : HasFDerivAt (angleLagrangian m₁ m₂ l₁ l₂ g t x) _ v :=
    hF.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => by
      simp only [angleLagrangian, lagrangian_eq, Pi.add_apply, Pi.mul_apply]; ring)
  rw [gradient_eq_two, hL.fderiv]
  ext i
  fin_cases i
  · simp; ring
  · simp; ring

private lemma differentiableAt_deriv_of_contDiffAt_two {q : Time → ℝ²} {t : Time}
    (hq : ContDiffAt ℝ 2 q t) : DifferentiableAt ℝ (∂ₜ q) t := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ q) t := hq.fderiv_right (m := 1) (by norm_num)
  exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const (1 : Time))

private lemma hasFDerivAt_comp_coord {f : Time → ℝ²} {t : Time} (hf : DifferentiableAt ℝ f t)
    (i : Fin 2) :
    HasFDerivAt (fun s => f s i) ((EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).comp (fderiv ℝ f t)) t :=
  (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).hasFDerivAt.comp t hf.hasFDerivAt

/-- The time derivative of the generalized momentum `M(q) q̇` along a trajectory `C²` at `t`. -/
private lemma deriv_gradient_angleLagrangian_right (m₁ m₂ l₁ l₂ g : ℝ) {q : Time → ℝ²} {t : Time}
    (hq : ContDiffAt ℝ 2 q t) :
    ∂ₜ (fun t' => gradient (angleLagrangian m₁ m₂ l₁ l₂ g t' (q t')) (∂ₜ q t')) t =
      !₂[(m₁ + m₂) * l₁ ^ 2 * ∂ₜ (∂ₜ q) t 0 + m₂ * l₁ * l₂ * (Real.cos (q t 0 - q t 1) *
            ∂ₜ (∂ₜ q) t 1 - Real.sin (q t 0 - q t 1) * (∂ₜ q t 0 - ∂ₜ q t 1) * ∂ₜ q t 1),
        m₂ * l₁ * l₂ * (Real.cos (q t 0 - q t 1) * ∂ₜ (∂ₜ q) t 0 -
            Real.sin (q t 0 - q t 1) * (∂ₜ q t 0 - ∂ₜ q t 1) * ∂ₜ q t 0) +
          m₂ * l₂ ^ 2 * ∂ₜ (∂ₜ q) t 1] := by
  have hqd : DifferentiableAt ℝ q t := hq.differentiableAt (by norm_num)
  have hvd : DifferentiableAt ℝ (∂ₜ q) t := differentiableAt_deriv_of_contDiffAt_two hq
  have hq0 := hasFDerivAt_comp_coord hqd 0
  have hq1 := hasFDerivAt_comp_coord hqd 1
  have hv0 := hasFDerivAt_comp_coord hvd 0
  have hv1 := hasFDerivAt_comp_coord hvd 1
  have hc := (hq0.sub hq1).cos
  have hΦ0 := (hv0.const_mul ((m₁ + m₂) * l₁ ^ 2)).add ((hc.const_mul (m₂ * l₁ * l₂)).mul hv1)
  have hΦ1 := ((hc.const_mul (m₂ * l₁ * l₂)).mul hv0).add (hv1.const_mul (m₂ * l₂ ^ 2))
  have hΦ := (hΦ0.smul_const (!₂[1, 0] : ℝ²)).add (hΦ1.smul_const (!₂[0, 1] : ℝ²))
  have hΦ' : HasFDerivAt
      (fun t' => gradient (angleLagrangian m₁ m₂ l₁ l₂ g t' (q t')) (∂ₜ q t')) _ t :=
    hΦ.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
      simp only [gradient_angleLagrangian_right]
      ext i; fin_cases i <;> simp)
  rw [Time.deriv_eq, hΦ'.fderiv]
  ext i; fin_cases i <;> simp [Time.deriv_eq] <;> ring

/-- The Euler-Lagrange operator of the two-link Lagrangian along an angle trajectory that is `C²` at
`t` is `f(q, q̇) - M(q) q̈`, for any real parameters. -/
lemma eulerLagrangeOp_angleLagrangian (m₁ m₂ l₁ l₂ g : ℝ) {q : Time → ℝ²} {t : Time}
    (hq : ContDiffAt ℝ 2 q t) :
    eulerLagrangeOp (angleLagrangian m₁ m₂ l₁ l₂ g) q t =
      generalizedForce m₁ m₂ l₁ l₂ g (q t) (∂ₜ q t) -
        WithLp.toLp 2 (massMatrix m₁ m₂ l₁ l₂ (q t 0) (q t 1) *ᵥ (∂ₜ (∂ₜ q) t).ofLp) := by
  simp only [ClassicalMechanics.eulerLagrangeOp_eq, gradient_angleLagrangian_left]
  rw [deriv_gradient_angleLagrangian_right m₁ m₂ l₁ l₂ g hq]
  ext i; fin_cases i <;>
    simp [generalizedForce, massMatrix, dotProduct, Fin.sum_univ_two] <;> ring

/-- For positive masses and lengths and an angle trajectory that is `C²` at `t`, the Euler-Lagrange
equation at `t` is the reduced ODE `q̈ = M(q)⁻¹ f(q, q̇)`. -/
lemma eulerLagrangeOp_angleLagrangian_eq_zero_iff {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (g : ℝ) {q : Time → ℝ²} {t : Time} (hq : ContDiffAt ℝ 2 q t) :
    eulerLagrangeOp (angleLagrangian m₁ m₂ l₁ l₂ g) q t = 0 ↔
      ∂ₜ (∂ₜ q) t = reducedAccel m₁ m₂ l₁ l₂ g (q t) (∂ₜ q t) := by
  rw [eulerLagrangeOp_angleLagrangian m₁ m₂ l₁ l₂ g hq, sub_eq_zero,
    ← mulVec_eq_iff_eq_reducedAccel hm₁ hm₂ hl₁ hl₂ g (q t) (∂ₜ q t)]
  constructor
  · intro h; rw [h]
  · intro h; rw [h]

/-! ## I. Newton's equations with rod reactions -/

/-- The Cartesian motion `t ↦ posMap (q₁ t, q₂ t)` of the two masses along an angle trajectory. -/
noncomputable def cartesianMotion (l₁ l₂ : ℝ) (q : Time → ℝ²) (t : Time) : ℝ² × ℝ² :=
  posMap l₁ l₂ (q t 0, q t 1)

/-- Gravity on the two masses, `(m₁ (0, -g), m₂ (0, -g))`: minus the Cartesian gradient of the
potential energy `g (m₁ y₁ + m₂ y₂)`. -/
noncomputable def gravityForce (m₁ m₂ g : ℝ) : ℝ² × ℝ² :=
  (m₁ • !₂[0, -g], m₂ • !₂[0, -g])

/-- The Cartesian accelerations of the two masses at angles `q`, angular velocities `w` and angular
accelerations `a`. -/
private noncomputable def cartAccel (l₁ l₂ : ℝ) (q w a : ℝ²) : ℝ² × ℝ² :=
  (!₂[l₁ * a 0 * Real.cos (q 0) - l₁ * w 0 ^ 2 * Real.sin (q 0),
      l₁ * a 0 * Real.sin (q 0) + l₁ * w 0 ^ 2 * Real.cos (q 0)],
    !₂[l₁ * a 0 * Real.cos (q 0) - l₁ * w 0 ^ 2 * Real.sin (q 0) +
        (l₂ * a 1 * Real.cos (q 1) - l₂ * w 1 ^ 2 * Real.sin (q 1)),
      l₁ * a 0 * Real.sin (q 0) + l₁ * w 0 ^ 2 * Real.cos (q 0) +
        (l₂ * a 1 * Real.sin (q 1) + l₂ * w 1 ^ 2 * Real.cos (q 1))])

private lemma deriv_cartesianMotion (l₁ l₂ : ℝ) {q : Time → ℝ²} {s : Time}
    (hq : DifferentiableAt ℝ q s) :
    ∂ₜ (cartesianMotion l₁ l₂ q) s =
      (vel₁ l₁ (q s 0) (∂ₜ q s 0), vel₂ l₁ l₂ (q s 0) (q s 1) (∂ₜ q s 0) (∂ₜ q s 1)) := by
  have h : HasFDerivAt (cartesianMotion l₁ l₂ q) _ s :=
    (hasFDerivAt_posMap l₁ l₂ (q s 0, q s 1)).comp s
      ((hasFDerivAt_comp_coord hq 0).prodMk (hasFDerivAt_comp_coord hq 1))
  rw [Time.deriv_eq, h.fderiv, ContinuousLinearMap.comp_apply, angleJacobian_apply]
  rfl

private lemma deriv_deriv_cartesianMotion (l₁ l₂ : ℝ) {q : Time → ℝ²} {t : Time}
    (hq : ContDiffAt ℝ 2 q t) :
    ∂ₜ (∂ₜ (cartesianMotion l₁ l₂ q)) t = cartAccel l₁ l₂ (q t) (∂ₜ q t) (∂ₜ (∂ₜ q) t) := by
  have hev : ∂ₜ (cartesianMotion l₁ l₂ q) =ᶠ[𝓝 t] fun s =>
      (vel₁ l₁ (q s 0) (∂ₜ q s 0), vel₂ l₁ l₂ (q s 0) (q s 1) (∂ₜ q s 0) (∂ₜ q s 1)) :=
    (hq.eventually (by simp)).mono fun s hs => deriv_cartesianMotion l₁ l₂ (hs.differentiableAt
      (by norm_num))
  have hqd : DifferentiableAt ℝ q t := hq.differentiableAt (by norm_num)
  have hvd : DifferentiableAt ℝ (∂ₜ q) t := differentiableAt_deriv_of_contDiffAt_two hq
  have hq0 := hasFDerivAt_comp_coord hqd 0
  have hq1 := hasFDerivAt_comp_coord hqd 1
  have hv0 := hasFDerivAt_comp_coord hvd 0
  have hv1 := hasFDerivAt_comp_coord hvd 1
  have hV₁ := (((hv0.const_mul l₁).mul hq0.cos).smul_const (!₂[1, 0] : ℝ²)).add
    (((hv0.const_mul l₁).mul hq0.sin).smul_const (!₂[0, 1] : ℝ²))
  have hV₂ := (hV₁.add (((hv1.const_mul l₂).mul hq1.cos).smul_const (!₂[1, 0] : ℝ²))).add
    (((hv1.const_mul l₂).mul hq1.sin).smul_const (!₂[0, 1] : ℝ²))
  have hV : HasFDerivAt (fun s =>
      (vel₁ l₁ (q s 0) (∂ₜ q s 0), vel₂ l₁ l₂ (q s 0) (q s 1) (∂ₜ q s 0) (∂ₜ q s 1))) _ t :=
    (hV₁.prodMk hV₂).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
      refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [vel₁, vel₂])
  rw [Time.deriv_eq, hev.fderiv_eq, hV.fderiv]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [cartAccel, Time.deriv_eq] <;> ring

/-- d'Alembert-Lagrange: the virtual work of the Newton residual `m a - F_gravity` along the
velocity `angleJacobian q u` is `u ⬝ (M(q) a - f(q, w))`. -/
private lemma virtualWork_newton (m₁ m₂ l₁ l₂ g : ℝ) (q w a u : ℝ²) :
    virtualWork ((m₁ • (cartAccel l₁ l₂ q w a).1, m₂ • (cartAccel l₁ l₂ q w a).2) -
        gravityForce m₁ m₂ g) (angleJacobian l₁ l₂ (q 0, q 1) (u 0, u 1)) =
      u 0 * ((massMatrix m₁ m₂ l₁ l₂ (q 0) (q 1) *ᵥ a.ofLp) 0 -
          generalizedForce m₁ m₂ l₁ l₂ g q w 0) +
        u 1 * ((massMatrix m₁ m₂ l₁ l₂ (q 0) (q 1) *ᵥ a.ofLp) 1 -
          generalizedForce m₁ m₂ l₁ l₂ g q w 1) := by
  have hs0 := Real.sin_sq_add_cos_sq (q 0)
  have hs1 := Real.sin_sq_add_cos_sq (q 1)
  rw [angleJacobian_apply]
  simp [virtualWork, cartAccel, gravityForce, vel₁, vel₂, massMatrix, generalizedForce,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, PiLp.inner_apply, Real.cos_sub, Real.sin_sub]
  linear_combination ((m₁ + m₂) * l₁ ^ 2 * a 0 * u 0) * hs0 + (m₂ * l₂ ^ 2 * a 1 * u 1) * hs1

private lemma newton_iff_residual (m₁ m₂ g : ℝ) (A R : ℝ² × ℝ²) :
    (m₁ • A.1, m₂ • A.2) = gravityForce m₁ m₂ g + R ↔
      (m₁ • A.1, m₂ • A.2) - gravityForce m₁ m₂ g = R := by
  rw [sub_eq_iff_eq_add']

/-- Newton's equations with some rod reaction force the reduced ODE. -/
private lemma eq_reducedAccel_of_newton {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (g : ℝ) (q w a : ℝ²) (c : ℝ × ℝ)
    (hc : (m₁ • (cartAccel l₁ l₂ q w a).1, m₂ • (cartAccel l₁ l₂ q w a).2) =
      gravityForce m₁ m₂ g + rodReaction c.1 c.2 (posMap l₁ l₂ (q 0, q 1))) :
    a = reducedAccel m₁ m₂ l₁ l₂ g q w := by
  rw [← mulVec_eq_iff_eq_reducedAccel hm₁ hm₂ hl₁ hl₂]
  have hN := (newton_iff_residual m₁ m₂ g _ _).mp hc
  have key : ∀ u : ℝ², u 0 * ((massMatrix m₁ m₂ l₁ l₂ (q 0) (q 1) *ᵥ a.ofLp) 0 -
      generalizedForce m₁ m₂ l₁ l₂ g q w 0) + u 1 * ((massMatrix m₁ m₂ l₁ l₂ (q 0) (q 1) *ᵥ
      a.ofLp) 1 - generalizedForce m₁ m₂ l₁ l₂ g q w 1) = 0 := fun u => by
    rw [← virtualWork_newton, hN]
    exact virtualWork_rodReaction_angleJacobian c.1 c.2 l₁ l₂ _ _
  ext i
  fin_cases i
  · have h := key !₂[1, 0]; simp at h; simp; linarith
  · have h := key !₂[0, 1]; simp at h; simp; linarith

/-- The reduced ODE gives Newton's equations with unique rod multipliers. -/
private lemma existsUnique_newton_of_eq_reducedAccel {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (g : ℝ) (q w a : ℝ²)
    (h : a = reducedAccel m₁ m₂ l₁ l₂ g q w) :
    ∃! c : ℝ × ℝ, (m₁ • (cartAccel l₁ l₂ q w a).1, m₂ • (cartAccel l₁ l₂ q w a).2) =
      gravityForce m₁ m₂ g + rodReaction c.1 c.2 (posMap l₁ l₂ (q 0, q 1)) := by
  have hMa := (mulVec_eq_iff_eq_reducedAccel hm₁ hm₂ hl₁ hl₂ g q w a).mpr h
  have hF : ∀ v, rodJacobian (posMap l₁ l₂ (q 0, q 1)) v = 0 →
      virtualWork ((m₁ • (cartAccel l₁ l₂ q w a).1, m₂ • (cartAccel l₁ l₂ q w a).2) -
        gravityForce m₁ m₂ g) v = 0 := by
    intro v hv
    have hmem : v ∈ LinearMap.range (angleJacobian l₁ l₂ (q 0, q 1)).toLinearMap := by
      rw [range_angleJacobian hl₁ hl₂]; exact hv
    obtain ⟨d, rfl⟩ := hmem
    have e := virtualWork_newton m₁ m₂ l₁ l₂ g q w a !₂[d.1, d.2]
    rw [hMa] at e
    simpa using e
  obtain ⟨c, hc, huniq⟩ := existsUnique_rodReaction hl₁ hl₂ (q 0, q 1) hF
  exact ⟨c, (newton_iff_residual m₁ m₂ g _ _).mpr hc,
    fun c' hc' => huniq c' ((newton_iff_residual m₁ m₂ g _ _).mp hc')⟩

/-- For positive masses and lengths, Newton's equations `mᵢ p̈ᵢ = mᵢ (0, -g) + Rᵢ` of the two
masses along the Cartesian motion of an angle trajectory that is `C²` at `t` hold at `t` with some
rod reaction `R` exactly when the angles satisfy the reduced ODE at `t`. -/
lemma exists_rodReaction_newton_iff {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) (g : ℝ) {q : Time → ℝ²} {t : Time} (hq : ContDiffAt ℝ 2 q t) :
    (∃ c : ℝ × ℝ, (m₁ • (∂ₜ (∂ₜ (cartesianMotion l₁ l₂ q)) t).1,
        m₂ • (∂ₜ (∂ₜ (cartesianMotion l₁ l₂ q)) t).2) =
        gravityForce m₁ m₂ g + rodReaction c.1 c.2 (cartesianMotion l₁ l₂ q t)) ↔
      ∂ₜ (∂ₜ q) t = reducedAccel m₁ m₂ l₁ l₂ g (q t) (∂ₜ q t) := by
  rw [deriv_deriv_cartesianMotion l₁ l₂ hq]
  exact ⟨fun ⟨c, hc⟩ => eq_reducedAccel_of_newton hm₁ hm₂ hl₁ hl₂ g _ _ _ c hc,
    fun h => (existsUnique_newton_of_eq_reducedAccel hm₁ hm₂ hl₁ hl₂ g _ _ _ h).exists⟩

/-- For positive masses and lengths and an angle trajectory that is `C²` at `t`, Newton's
equations hold at `t` with exactly one pair of rod multipliers exactly when the angles satisfy the
reduced ODE at `t`: along solutions of the reduced ODE the rod multipliers are unique. -/
lemma existsUnique_rodReaction_newton_iff {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (g : ℝ) {q : Time → ℝ²} {t : Time} (hq : ContDiffAt ℝ 2 q t) :
    (∃! c : ℝ × ℝ, (m₁ • (∂ₜ (∂ₜ (cartesianMotion l₁ l₂ q)) t).1,
        m₂ • (∂ₜ (∂ₜ (cartesianMotion l₁ l₂ q)) t).2) =
        gravityForce m₁ m₂ g + rodReaction c.1 c.2 (cartesianMotion l₁ l₂ q t)) ↔
      ∂ₜ (∂ₜ q) t = reducedAccel m₁ m₂ l₁ l₂ g (q t) (∂ₜ q t) := by
  rw [deriv_deriv_cartesianMotion l₁ l₂ hq]
  exact ⟨fun h => eq_reducedAccel_of_newton hm₁ hm₂ hl₁ hl₂ g _ _ _ h.exists.choose
      h.exists.choose_spec,
    fun h => existsUnique_newton_of_eq_reducedAccel hm₁ hm₂ hl₁ hl₂ g _ _ _ h⟩

/-! ## J. Local regularity and the local initial value problem -/

/-- The reduced first-order field on states `x = (q, w)` of angles and angular velocities:
`(q, w) ↦ (w, M(q)⁻¹ f(q, w))`. Where `det M(q) = 0` (for example `m₂ = 0` or a length `0`),
`M(q)⁻¹ = 0` and the field is `(w, 0)`. -/
noncomputable def reducedField (m₁ m₂ l₁ l₂ g : ℝ) (x : ℝ² × ℝ²) : ℝ² × ℝ² :=
  (x.2, reducedAccel m₁ m₂ l₁ l₂ g x.1 x.2)

private lemma contDiff_coord_fst (i : Fin 2) :
    ContDiff ℝ ∞ (fun x : ℝ² × ℝ² => x.1 i) :=
  (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).contDiff.comp contDiff_fst

private lemma contDiff_coord_snd (i : Fin 2) :
    ContDiff ℝ ∞ (fun x : ℝ² × ℝ² => x.2 i) :=
  (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).contDiff.comp contDiff_snd

/-- For positive masses and lengths the reduced field is smooth on the whole state space, collinear
links included. -/
lemma contDiff_reducedField {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) (g : ℝ) : ContDiff ℝ ∞ (reducedField m₁ m₂ l₁ l₂ g) := by
  have h0 := contDiff_coord_fst 0
  have h1 := contDiff_coord_fst 1
  have v0 := contDiff_coord_snd 0
  have v1 := contDiff_coord_snd 1
  have hD : ∀ x : ℝ² × ℝ², l₁ ^ 2 * l₂ ^ 2 * m₂ * (m₁ + m₂ * Real.sin (x.1 0 - x.1 1) ^ 2) ≠ 0 :=
    fun x => (det_pos' hm₁ hm₂ hl₁ hl₂ _).ne'
  refine contDiff_snd.prodMk (contDiff_euclidean.mpr fun i => ?_)
  fin_cases i
  · simp only [reducedAccel, generalizedForce, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta]
    exact ContDiff.div (by fun_prop) (by fun_prop) hD
  · simp only [reducedAccel, generalizedForce, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.mk_one]
    exact ContDiff.div (by fun_prop) (by fun_prop) hD

/-- For positive masses and lengths the reduced field is locally Lipschitz, the regularity
hypothesis of the Picard-Lindelöf theorem. -/
lemma locallyLipschitz_reducedField {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (g : ℝ) : LocallyLipschitz (reducedField m₁ m₂ l₁ l₂ g) := by
  exact ((contDiff_reducedField hm₁ hm₂ hl₁ hl₂ g).of_le (by simp)).locallyLipschitz

/-- Local Picard existence: for positive masses and lengths, every state `x₀` at every time `t₀`
starts a solution of the reduced field on an open interval `(t₀ - ε, t₀ + ε)` with `ε > 0`. -/
lemma exists_forall_mem_Ioo_hasDerivAt_reducedField {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (g t₀ : ℝ) (x₀ : ℝ² × ℝ²) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → ℝ² × ℝ², α t₀ = x₀ ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (reducedField m₁ m₂ l₁ l₂ g (α t)) t := by
  have hf : ContDiffAt ℝ 1 (reducedField m₁ m₂ l₁ l₂ g) x₀ :=
    ((contDiff_reducedField hm₁ hm₂ hl₁ hl₂ g).of_le (by simp)).contDiffAt
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  obtain ⟨α, hα₀, hα⟩ :=
    (hpl t₀).exists_eq_forall_mem_Icc_hasDerivWithinAt (Metric.mem_closedBall_self r.2)
  exact ⟨ε, hε, α, hα₀, fun t ht =>
    (hα t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

private lemma deriv_comp_val {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : ℝ → E}
    {v : E} {s : Time} (h : HasDerivAt γ v s.val) : ∂ₜ (fun s : Time => γ s.val) s = v :=
  Time.deriv_comp_toRealCLE_of_hasDerivAt γ s v h

/-- The local initial value problem of the Euler-Lagrange equation: for positive masses and
lengths, initial angles `q₀` and angular velocities `w₀` at `t₀` start an angle trajectory that is
`C²` at every instant of an open interval around `t₀` and along which the Euler-Lagrange operator
vanishes. -/
lemma exists_eulerLagrangeOp_angleLagrangian_eq_zero {m₁ m₂ l₁ l₂ : ℝ} (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (g : ℝ) (t₀ : Time) (q₀ w₀ : ℝ²) :
    ∃ ε > (0 : ℝ), ∃ q : Time → ℝ², q t₀ = q₀ ∧ ∂ₜ q t₀ = w₀ ∧
      ∀ t : Time, t.val ∈ Set.Ioo (t₀.val - ε) (t₀.val + ε) →
        ContDiffAt ℝ 2 q t ∧ eulerLagrangeOp (angleLagrangian m₁ m₂ l₁ l₂ g) q t = 0 := by
  have hF := contDiff_reducedField hm₁ hm₂ hl₁ hl₂ g
  have hf : ContDiffAt ℝ 1 (reducedField m₁ m₂ l₁ l₂ g) (q₀, w₀) :=
    (hF.of_le (by simp)).contDiffAt
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  obtain ⟨α, hα₀, hα⟩ :=
    (hpl t₀.val).exists_eq_forall_mem_Icc_hasDerivWithinAt (Metric.mem_closedBall_self r.2)
  have hC : ContDiffOn ℝ 2 α (Set.Icc (t₀.val - ε) (t₀.val + ε)) :=
    ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := 2) (u := Set.univ)
      ((hF.of_le (by simp)).comp contDiff_snd).contDiffOn hα (Set.mapsTo_univ _ _)
  have hD : ∀ τ ∈ Set.Ioo (t₀.val - ε) (t₀.val + ε),
      HasDerivAt α (reducedField m₁ m₂ l₁ l₂ g (α τ)) τ := fun τ hτ =>
    (hα τ (Set.Ioo_subset_Icc_self hτ)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
  have hD₁ : ∀ τ ∈ Set.Ioo (t₀.val - ε) (t₀.val + ε), HasDerivAt (fun τ => (α τ).1) (α τ).2 τ :=
    fun τ hτ => (hasFDerivAt_fst (𝕜 := ℝ) (p := α τ)).comp_hasDerivAt τ (hD τ hτ)
  have hD₂ : ∀ τ ∈ Set.Ioo (t₀.val - ε) (t₀.val + ε),
      HasDerivAt (fun τ => (α τ).2) (reducedAccel m₁ m₂ l₁ l₂ g (α τ).1 (α τ).2) τ :=
    fun τ hτ => (hasFDerivAt_snd (𝕜 := ℝ) (p := α τ)).comp_hasDerivAt τ (hD τ hτ)
  have hv : ∀ s : Time, s.val ∈ Set.Ioo (t₀.val - ε) (t₀.val + ε) →
      ∂ₜ (fun s : Time => (α s.val).1) s = (α s.val).2 := fun s hs =>
    deriv_comp_val (hD₁ s.val hs)
  have hmem : t₀.val ∈ Set.Ioo (t₀.val - ε) (t₀.val + ε) := ⟨by linarith, by linarith⟩
  refine ⟨ε, hε, fun s => (α s.val).1, by simp [hα₀], by rw [hv t₀ hmem, hα₀], fun t ht => ?_⟩
  have hCt : ContDiffAt ℝ 2 (fun s : Time => (α s.val).1) t :=
    ((contDiff_fst.comp_contDiffOn hC).contDiffAt (Icc_mem_nhds ht.1 ht.2)).comp t
      (Time.val_contDiff (n := 2)).contDiffAt
  refine ⟨hCt, (eulerLagrangeOp_angleLagrangian_eq_zero_iff hm₁ hm₂ hl₁ hl₂ g hCt).mpr ?_⟩
  have hev : ∂ₜ (fun s : Time => (α s.val).1) =ᶠ[𝓝 t] fun s : Time => (α s.val).2 :=
    Filter.mem_of_superset ((Time.val_contDiff (n := 0)).continuous.continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds ht.1 ht.2)) fun s hs => hv s hs
  rw [Time.deriv_eq, hev.fderiv_eq, ← Time.deriv_eq, deriv_comp_val (hD₂ t.val ht), hv t ht]

end PhyslibExt.Mechanics.ConstrainedTwoLink
