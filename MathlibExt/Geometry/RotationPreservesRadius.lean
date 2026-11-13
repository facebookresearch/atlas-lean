/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Fin.VecNotation

/-!
# Rotation preserves radius

An orthogonal matrix `Q` (`Q * Qᵀ = 1`) preserves the squared radius
`∑ i, (Q *ᵥ x) i ^ 2` of any vector `x : Fin 3 → ℝ`.

## i. Overview

Both squared radii are dot products with themselves. Moving `Q` across the
dot product (`Matrix.dotProduct_mulVec`, `Matrix.vecMul_mulVec`) turns the
rotated dot product into `x ⬝ᵥ (Qᵀ * Q) x`, and `Qᵀ * Q = 1` follows from
`Q * Qᵀ = 1` by `mul_eq_one_comm`.

## ii. Key results

- `EarthScience.rotation_preserves_radius_sq`: a rotation preserves the
  squared radius.

## iii. References

- `Matrix.dotProduct_mulVec`, `Matrix.vecMul_mulVec`, `mul_eq_one_comm`
  (Mathlib).
-/

@[expose] public section

open Matrix
open scoped BigOperators

namespace EarthScience

/-- A rotation (orthogonal matrix) preserves radius: the squared radius
`∑ i, (Q *ᵥ x) i ^ 2` of a rotated vector equals that of `x`. -/
theorem rotation_preserves_radius_sq {Q : Matrix (Fin 3) (Fin 3) ℝ}
    (hQ : Q * Matrix.transpose Q = 1) (x : Fin 3 → ℝ) :
    ∑ i, (Matrix.mulVec Q x i) ^ 2 = ∑ i, (x i) ^ 2 := by
  have hQtQ : Matrix.transpose Q * Q = 1 := mul_eq_one_comm.mp hQ
  have hsq : ∀ (y : Fin 3 → ℝ), ∑ i, (y i) ^ 2 = dotProduct y y := by
    intro y
    simp only [dotProduct, pow_two]
  rw [hsq, hsq]
  calc dotProduct (Matrix.mulVec Q x) (Matrix.mulVec Q x)
      = dotProduct (Matrix.vecMul (Matrix.mulVec Q x) Q) x := by
        rw [Matrix.dotProduct_mulVec]
    _ = dotProduct (Matrix.vecMul x (Matrix.transpose Q * Q)) x := by
        rw [Matrix.vecMul_mulVec]
    _ = dotProduct (Matrix.vecMul x 1) x := by rw [hQtQ]
    _ = dotProduct x x := by rw [Matrix.vecMul_one]

end EarthScience
