/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.QuaternionRotation
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Quaternion axis-angle rotation formula

For a unit axis `u : Fin 3 → ℝ` and an angle `θ`, the quaternion
`cos (θ / 2) + sin (θ / 2) * u` acts by conjugation on pure quaternions as
the rotation about `u` through `θ`, in Rodrigues form.

Reference: Stanford CS348a, Handout #12, "Representing rotations with quaternions".
-/

@[expose] public section

open Quaternion

namespace QuaternionRotation

/-- The quaternion `cos (θ / 2) + sin (θ / 2) * u` for rotation through angle
`θ` about axis `u`, as the linear combination of `1`, `i`, `j`, `k` those
components encode; it has norm `1` when `u` is a unit axis. -/
noncomputable def axisAngle (u : Fin 3 → ℝ) (θ : ℝ) : ℍ :=
  ⟨Real.cos (θ / 2), Real.sin (θ / 2) * u 0, Real.sin (θ / 2) * u 1, Real.sin (θ / 2) * u 2⟩

/-- The axis-angle quaternion over a unit axis has norm `1`. -/
theorem norm_axisAngle {u : Fin 3 → ℝ} (hu : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1) (θ : ℝ) :
    ‖axisAngle u θ‖ = 1 := by
  have hcs : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have hnsq : Quaternion.normSq (axisAngle u θ) = 1 := by
    rw [Quaternion.normSq_def']
    change Real.cos (θ / 2) ^ 2 + (Real.sin (θ / 2) * u 0) ^ 2 +
        (Real.sin (θ / 2) * u 1) ^ 2 + (Real.sin (θ / 2) * u 2) ^ 2 = 1
    linear_combination hcs + (Real.sin (θ / 2) ^ 2) * hu
  rw [Quaternion.normSq_eq_norm_mul_self] at hnsq
  have hnn : 0 ≤ ‖axisAngle u θ‖ := norm_nonneg _
  have hfac : (‖axisAngle u θ‖ - 1) * (‖axisAngle u θ‖ + 1) = 0 := by
    linear_combination hnsq
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith

/-- Fin-mk index `2` as an `OfNat` literal, for `simp only` entry reduction. -/
private theorem fin_mk_two_eq {h : 2 < 3} : (⟨2, h⟩ : Fin 3) = 2 := rfl

/-- Conjugation matrix of a quaternion given by explicit components. -/
private theorem rotMatrix_mk (a b c d : ℝ) :
    rotMatrix ⟨a, b, c, d⟩ =
      !![a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2, 2 * b * c - 2 * a * d, 2 * b * d + 2 * a * c;
         2 * b * c + 2 * a * d, a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2, 2 * c * d - 2 * a * b;
         2 * b * d - 2 * a * c, 2 * c * d + 2 * a * b, a ^ 2 - b ^ 2 - c ^ 2 + d ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMatrix, imCoords, imBasis, Matrix.cons_val_two] <;> ring

/-- The rotation matrix of an axis-angle quaternion is the Rodrigues matrix:
`cos θ` on the scaled identity plus the skew and outer terms in `u`. -/
theorem rotMatrix_axisAngle {u : Fin 3 → ℝ} (hu : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1) (θ : ℝ) :
    rotMatrix (axisAngle u θ) =
      !![Real.cos θ + (1 - Real.cos θ) * u 0 ^ 2,
         (1 - Real.cos θ) * u 0 * u 1 - Real.sin θ * u 2,
         (1 - Real.cos θ) * u 0 * u 2 + Real.sin θ * u 1;
         (1 - Real.cos θ) * u 1 * u 0 + Real.sin θ * u 2,
         Real.cos θ + (1 - Real.cos θ) * u 1 ^ 2,
         (1 - Real.cos θ) * u 1 * u 2 - Real.sin θ * u 0;
         (1 - Real.cos θ) * u 2 * u 0 - Real.sin θ * u 1,
         (1 - Real.cos θ) * u 2 * u 1 + Real.sin θ * u 0,
         Real.cos θ + (1 - Real.cos θ) * u 2 ^ 2] := by
  have hθ : θ = 2 * (θ / 2) := by ring
  have hc : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    conv_lhs => rw [hθ, Real.cos_two_mul']
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    conv_lhs => rw [hθ, Real.sin_two_mul]
  have h1c : 1 - Real.cos θ = 2 * Real.sin (θ / 2) ^ 2 := by
    conv_lhs => rw [hθ, Real.cos_two_mul_eq_one_sub]
    ring
  unfold axisAngle
  rw [rotMatrix_mk, h1c, hc, hs]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.of_apply, Matrix.cons_val_zero, Fin.mk_zero]
    linear_combination (-(Real.sin (θ / 2) ^ 2)) * hu
  · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one]
    ring
  · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.mk_zero, fin_mk_two_eq]
    ring
  · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one]
    ring
  · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_one]
    linear_combination (-(Real.sin (θ / 2) ^ 2)) * hu
  · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.mk_one, fin_mk_two_eq]
    ring
  · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.mk_zero, fin_mk_two_eq]
    ring
  · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.mk_one, fin_mk_two_eq]
    ring
  · simp only [Matrix.of_apply, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      fin_mk_two_eq]
    linear_combination (-(Real.sin (θ / 2) ^ 2)) * hu

/-- Applying the axis-angle rotation matrix is the Rodrigues vector formula:
`cos θ` times `v`, plus `sin θ` times the cross product, plus the projected axis term. -/
theorem rotMatrix_axisAngle_mulVec {u v : Fin 3 → ℝ}
    (hu : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1) (θ : ℝ) :
    Matrix.mulVec (rotMatrix (axisAngle u θ)) v =
      Real.cos θ • v + Real.sin θ • crossProduct u v +
        (1 - Real.cos θ) • ((dotProduct u v) • u) := by
  rw [rotMatrix_axisAngle hu θ]
  funext i
  fin_cases i
  · simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three, cross_apply, Matrix.vec3_dotProduct,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Pi.add_apply, Pi.smul_apply, Fin.mk_zero]
    ring
  · simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three, cross_apply, Matrix.vec3_dotProduct,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Pi.add_apply, Pi.smul_apply, Fin.mk_one]
    ring
  · simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three, cross_apply, Matrix.vec3_dotProduct,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Pi.add_apply, Pi.smul_apply, fin_mk_two_eq]
    ring

/-- The axis-angle rotation fixes its own axis. -/
theorem rotMatrix_axisAngle_mulVec_self {u : Fin 3 → ℝ}
    (hu : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1) (θ : ℝ) :
    Matrix.mulVec (rotMatrix (axisAngle u θ)) u = u := by
  have hdot : dotProduct u u = 1 := by
    rw [Matrix.vec3_dotProduct]
    linear_combination hu
  rw [rotMatrix_axisAngle_mulVec hu θ, cross_self, hdot]
  funext i
  simp [Pi.add_apply, Pi.smul_apply]
  ring

end QuaternionRotation
