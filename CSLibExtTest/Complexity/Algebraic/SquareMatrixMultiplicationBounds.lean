/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Complexity.Algebraic.SquareMatrixMultiplicationBounds

namespace CSLibExtTest.Complexity.Algebraic.SquareMatrixMultiplicationBounds

open Cslib.Complexity.Algebraic
open Cslib.Complexity.Algebraic.SquareMatrixMultiplicationBoundsWanted

#check @Cslib.Complexity.Algebraic.SquareMatrixMultiplicationBoundsWanted.squareOperationRankBridge
#print axioms Cslib.Complexity.Algebraic.SquareMatrixMultiplicationBoundsWanted.squareOperationRankBridge

example : squareMatrixMultiplicationCircuitExponent ℚ =
    MatrixMultiplicationExponent.matrixMultiplicationExponent ℚ :=
  squareOperationRankBridge ℚ

example : 2 ≤ MatrixMultiplicationExponent.matrixMultiplicationExponent ℚ := by
  rw [← squareOperationRankBridge ℚ]
  exact two_le_squareMatrixMultiplicationCircuitExponent ℚ

end CSLibExtTest.Complexity.Algebraic.SquareMatrixMultiplicationBounds
