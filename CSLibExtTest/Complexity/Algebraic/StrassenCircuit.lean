/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Complexity.Algebraic.StrassenCircuit
import Mathlib.Algebra.Field.ZMod

/-!
# Tests for Strassen's arithmetic circuits

The scalar base case takes one gate. A padded three-by-three product over the binary field
exercises subtraction in characteristic two and reads an output in the last row and column.
-/

namespace Cslib.Complexity.Algebraic.SquareMatrixMultiplicationBoundsWanted

example : ∃ c : MatrixArithmeticCircuit ℚ 1 1 1, IsMatrixMultiplication c ∧ c.size = 1 := by
  obtain ⟨c, hc, hs⟩ := padded_circuit ℚ 1 0 (by decide)
  exact ⟨c, hc, hs.antisymm (hc.output_cost_le 0)⟩

example :
    ∃ c : MatrixArithmeticCircuit (ZMod 2) 3 3 3, IsMatrixMultiplication c ∧ c.size ≤ 247 ∧
      c.evaluate (matrixInput (Matrix.of fun _ _ => 1) (Matrix.of fun _ _ => 1)) (2, 2) = 1 := by
  obtain ⟨c, hc, hs⟩ := padded_circuit (ZMod 2) 3 2 (by decide)
  refine ⟨c, hc, hs, ?_⟩
  rw [hc]
  decide

end Cslib.Complexity.Algebraic.SquareMatrixMultiplicationBoundsWanted
