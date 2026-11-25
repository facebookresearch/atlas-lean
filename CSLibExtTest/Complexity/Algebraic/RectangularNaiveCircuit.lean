/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Complexity.Algebraic.RectangularNaiveCircuit
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for naive rectangular matrix multiplication

The empty inner dimension costs no gates. A product with three summands checks the
accumulation and output indexing, and aspect one half checks the exponent bound.
-/

namespace Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted

example : ∃ c : MatrixArithmeticCircuit ℚ 2 0 2, c.size = 0 ∧
    ∀ A B i j, c.evaluate (matrixInput A B) (i, j) = 0 := by
  obtain ⟨c, hc, hs⟩ := naiveCircuit ℚ 2 0
  exact ⟨c, hs, fun A B i j => by simp [hc A B i j, Matrix.mul_apply]⟩

example :
    let A : Matrix (Fin 2) (Fin 3) ℚ := !![1, 2, 3; 4, 5, 6]
    let B : Matrix (Fin 3) (Fin 2) ℚ := !![1, 2; 2, 1; -1, 2]
    ∃ c : MatrixArithmeticCircuit ℚ 2 3 2, c.size = 24 ∧
      c.evaluate (matrixInput A B) (0, 1) = 10 ∧ c.evaluate (matrixInput A B) (1, 0) = 8 := by
  dsimp only
  obtain ⟨c, hc, hs⟩ := naiveCircuit ℚ 2 3
  refine ⟨c, hs, (hc _ _ 0 1).trans ?_, (hc _ _ 1 0).trans ?_⟩ <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_three]

example : rectangularCircuitExponent ℚ (1 / 2) ≤ ENNReal.ofReal (5 / 2) := by
  convert rectangularNaiveUpper ℚ (1 / 2) (by norm_num) using 2
  norm_num

end Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted
