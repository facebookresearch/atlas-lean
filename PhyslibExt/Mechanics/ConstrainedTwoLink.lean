/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibExt.Units.EngineeringFrames
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Two-link kinetic energy and regular reduced mass matrix

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

Model inputs: point masses on ideal massless rods; absolute link angles in one inertial frame, a
chosen coordinate model on all of `ℝ²` (periodic, not a global chart of the configuration
manifold); uniform gravity along the downward vertical; no friction and no actuation. Constraint
forces, the Euler-Lagrange equations and their initial value problem, chart-free or
differential-algebraic formulations, and empirical adequacy or system safety are not treated.

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

## iii. Table of contents

- A. Cartesian positions, rod constraints and the frame convention
- B. Velocities on actual angle trajectories
- C. Kinetic energy, potential energy and the Lagrangian
- D. The reduced mass matrix is regular

## iv. References

- L. D. Landau and E. M. Lifshitz, *Mechanics*, Section 5, Problem 1 (the Lagrangian of a
  coplanar double pendulum).
- H. Goldstein, C. Poole and J. Safko, *Classical Mechanics*, 3rd edition, chapter 1
  (constraints, generalized coordinates, and the kinetic energy as a quadratic form in the
  generalized velocities).
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

end PhyslibExt.Mechanics.ConstrainedTwoLink
