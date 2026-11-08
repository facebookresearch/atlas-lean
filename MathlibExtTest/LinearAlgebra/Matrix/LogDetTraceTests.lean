/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.LogDetTrace

/-!
# Tests for `Matrix.PosDef.log_det_mul_le_trace`

With `A = B = I` on `Fin 2` the inequality reads `log 1 ≤ 2 - 2`, and both sides are `0`
(the equality case `A = B⁻¹`).
-/

namespace MathlibExtTest.LogDetTrace

open Matrix

example : Real.log ((1 : Matrix (Fin 2) (Fin 2) ℝ).det * (1 : Matrix (Fin 2) (Fin 2) ℝ).det) ≤
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) * 1).trace - Fintype.card (Fin 2) :=
  PosDef.one.log_det_mul_le_trace PosDef.one

example : Real.log ((1 : Matrix (Fin 2) (Fin 2) ℝ).det * (1 : Matrix (Fin 2) (Fin 2) ℝ).det) = 0 ∧
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) * 1).trace - (Fintype.card (Fin 2) : ℝ) = 0 := by
  simp

end MathlibExtTest.LogDetTrace
