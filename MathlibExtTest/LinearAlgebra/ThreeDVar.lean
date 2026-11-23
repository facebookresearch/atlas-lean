/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.LinearAlgebra.ThreeDVar
public import Mathlib.Algebra.Order.Star.Real

/-!
# Tests for 3D-Var

Closed checks: `H = I, B = R = I` gives `xa = (xb + y) / 2`,
`H = 0` gives `xa = xb`, the scalar Woodbury identity, and the normal
equations on a concrete one-dimensional example.
-/

@[expose] public section

open Matrix

namespace MathlibExt.LinearAlgebra.ThreeDVar

/-- `H = I, B = R = I`: the minimizer is the midpoint `(xb + y) / 2`. -/
example (xb y : Fin 1 → ℝ) :
    Minimizer (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) xb y = (xb + y) / 2 := by
  ext i
  simp [Minimizer]
  ring

/-- `H = 0`: the minimizer is the background `xb`. -/
example (xb y : Fin 1 → ℝ) :
    Minimizer (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (0 : Matrix (Fin 1) (Fin 1) ℝ) xb y = xb := by
  simp [Minimizer]

/-- Scalar Woodbury identity with `B = R = 1`, `H = 1`: `(1 + 1)⁻¹ = 1 - 1 * (1 + 1)⁻¹ * 1`. -/
example : ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ +
      (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *
        (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ =
    (1 : Matrix (Fin 1) (Fin 1) ℝ) - (1 : Matrix (Fin 1) (Fin 1) ℝ) *
      (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ *
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
          (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ + (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ *
      (1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have h := woodbury (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) Matrix.PosDef.one Matrix.PosDef.one
  exact h

/-- Normal equations on a one-dimensional example: with `B = R = H = 1`, `xb = 0`
and `y = 2`, `normal_equation` reads `(1 + 1) (xa - 0) = 1 (2 - 0)`. -/
example :
    (2 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
        (Minimizer (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 ![2] - 0) = ![2] := by
  have h := normal_equation (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 ![2] Matrix.PosDef.one Matrix.PosDef.one
  have hlhs : ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ + (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ *
      (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * (1 : Matrix (Fin 1) (Fin 1) ℝ)) = 2 := by
    rw [inv_one, transpose_one, mul_one, mul_one, one_add_one_eq_two]
  rw [hlhs] at h
  rw [h]
  simp

#print axioms woodbury
#print axioms normal_equation
#print axioms minimizer_isMin_unique

end MathlibExt.LinearAlgebra.ThreeDVar
