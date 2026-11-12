/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.LinearAlgebra.G07ThreeDVar
public import Mathlib.Algebra.Order.Star.Real

/-!
# Tests for 3D-Var (G07)

Closed checks: `H = I, B = R = I` gives `xa = (xb + y) / 2`,
`H = 0` gives `xa = xb`, the scalar Woodbury identity, and the normal
equations on a concrete one-dimensional example.
-/

@[expose] public section

open Matrix

namespace MathlibExt.LinearAlgebra.G07ThreeDVar

/-- `H = I, B = R = I`: the minimizer is the midpoint `(xb + y) / 2`. -/
example (xb y : Fin 1 → ℝ) :
    g07Minimizer (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) xb y = (xb + y) / 2 := by
  ext i
  simp [g07Minimizer]
  ring

/-- `H = 0`: the minimizer is the background `xb`. -/
example (xb y : Fin 1 → ℝ) :
    g07Minimizer (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (0 : Matrix (Fin 1) (Fin 1) ℝ) xb y = xb := by
  simp [g07Minimizer]

/-- Scalar Woodbury identity with `B = R = 1`, `H = 1`: `(1 + 1)⁻¹ = 1 - 1 * (1 + 1)⁻¹ * 1`. -/
example : ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ +
      (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *
        (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ =
    (1 : Matrix (Fin 1) (Fin 1) ℝ) - (1 : Matrix (Fin 1) (Fin 1) ℝ) *
      (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ *
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
          (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ + (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ *
      (1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have h := g07_woodbury (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) Matrix.PosDef.one Matrix.PosDef.one
  exact h

/-- Normal equations on a one-dimensional example: `B = R = H = 1`,
`xb = 0`, `y = 2` gives `xa = 1` and `(1 + 1) * (1 - 0) = 1 * (2 - 0)`. -/
example :
    g07Minimizer (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 ![2] = ![1] := by
  have h := g07_minimizer_isMin_unique (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 ![2]
    Matrix.PosDef.one Matrix.PosDef.one ![1]
  -- The minimizer is the unique point attaining the minimum; show `![1]`
  -- attains the same cost as the minimizer, hence equals it.
  have hcost : g07Cost (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 ![2] ![1] =
      g07Cost (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 ![2]
        (g07Minimizer (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 ![2]) := by
    have hm : g07Minimizer (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 ![2] = ![1] := by
      ext i
      simp [g07Minimizer]
      ring
    rw [hm]
  exact (h.2 hcost).symm

#print axioms g07_woodbury
#print axioms g07_normal_equation
#print axioms g07_minimizer_isMin_unique

end MathlibExt.LinearAlgebra.G07ThreeDVar
