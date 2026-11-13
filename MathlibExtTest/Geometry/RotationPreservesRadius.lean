/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.RotationPreservesRadius

open scoped BigOperators

/-- The 90-degree rotation about the `z`-axis is orthogonal:
`Q * Qᵀ = 1`. -/
private theorem rot_z_90_orthogonal :
    (!![0, -1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ)
      * Matrix.transpose (!![0, -1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ)
      = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- Concrete non-vacuous case: rotating `(1, 2, 3)` by 90 degrees about the
`z`-axis gives `(-2, 1, 3)`, and both have squared radius `14`. -/
example : ∑ i, (Matrix.mulVec
    (!![0, -1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ)
    ![1, 2, 3] i) ^ 2 = 14 := by
  have h := EarthScience.rotation_preserves_radius_sq rot_z_90_orthogonal ![1, 2, 3]
  have hsum : ∑ i, (![1, 2, 3] i : ℝ) ^ 2 = 14 := by
    norm_num [Fin.sum_univ_three]
  rw [hsum] at h
  exact h

/-- Boundary case: the identity matrix is orthogonal and preserves every
radius, including the zero vector's radius `0`. -/
example : ∑ i, (Matrix.mulVec (1 : Matrix (Fin 3) (Fin 3) ℝ) ![0, 0, 0] i) ^ 2
    = ∑ i, (![0, 0, 0] i : ℝ) ^ 2 := by
  exact EarthScience.rotation_preserves_radius_sq (by simp) ![0, 0, 0]
