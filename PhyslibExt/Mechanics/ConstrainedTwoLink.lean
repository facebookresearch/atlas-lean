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
public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibExt.Units.EngineeringFrames
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Two-link kinetic energy, regular mass matrix, tangent space and rod reactions

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

Model inputs: point masses on ideal massless rods; absolute link angles in one inertial frame, a
chosen coordinate model on all of `ℝ²` (periodic, not a global chart of the configuration
manifold), with tangent spaces taken locally at a supplied configuration; uniform gravity along
the downward vertical; no friction and no actuation. Virtual velocities are the kernel vectors of
the constraint Jacobian, and a reaction is ideal when it does no virtual work along them
(d'Alembert's principle). The Euler-Lagrange equations and their initial value problem, general
constant-rank or manifold constraints, chart-free or differential-algebraic formulations, and
empirical adequacy or system safety are not treated.

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

## iii. Table of contents

- A. Cartesian positions, rod constraints and the frame convention
- B. Velocities on actual angle trajectories
- C. Kinetic energy, potential energy and the Lagrangian
- D. The reduced mass matrix is regular
- E. The rod constraints and their Jacobian
- F. The tangent space
- G. Rod reactions and virtual work

## iv. References

- L. D. Landau and E. M. Lifshitz, *Mechanics*, Section 5, Problem 1 (the Lagrangian of a
  coplanar double pendulum).
- H. Goldstein, C. Poole and J. Safko, *Classical Mechanics*, 3rd edition, chapter 1
  (constraints, generalized coordinates, and the kinetic energy as a quadratic form in the
  generalized velocities; Sections 1.3 and 1.4 for virtual displacements, d'Alembert's principle
  and workless constraint forces).
- `PhyslibExt.Units.EngineeringFrames` (frame convention) and `PhyslibExt.Mechanics.PowerPorts`
  (particle kinetic energy).
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

/-- The positions satisfy the two rod constraints `‖p₁‖ = l₁` and `‖p₂ - p₁‖ = l₂`. -/
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

/-- On an actual angle trajectory the kinetic energy of the actual Cartesian velocities, the time
derivatives of the positions, is `q'ᵀ M(q) q' / 2`. -/
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
`m₁ m₂ l₁² l₂²`: no rank loss for this open chain. -/
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
`g(p) = (‖p₁‖² - l₁², ‖p₂ - p₁‖² - l₂²)`; the rods of lengths `l₁, l₂` hold where `g(p) = 0`. -/
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

/-- The angle derivative sends angular velocities to the Cartesian velocities of the two-link
module. -/
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

/-- Every kernel vector at `posMap q` is the velocity at `s = 0` of the explicit constrained curve
`s ↦ posMap (q + s w)`, for exactly one angular velocity `w`. -/
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
with the opposite force. This is `(c₁ ∇g₁ + c₂ ∇g₂) / 2`; a tension `T₁ > 0` in the first rod is
`c₁ = -T₁ / l₁`, and a tension `T₂ > 0` in the second is `c₂ = -T₂ / l₂`. -/
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

end PhyslibExt.Mechanics.ConstrainedTwoLink
