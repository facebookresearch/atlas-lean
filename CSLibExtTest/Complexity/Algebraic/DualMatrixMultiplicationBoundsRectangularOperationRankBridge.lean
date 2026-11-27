/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.DualMatrixMultiplicationBoundsRectangularOperationRankBridge

set_option autoImplicit false

namespace CSLibExtTest.Complexity.Algebraic.DualMatrixMultiplicationBoundsRectangularOperationRankBridge

open Cslib.Complexity.Algebraic
open Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted

public theorem rational_zero :
    rectangularCircuitExponent ℚ 0 =
      MatrixMultiplicationExponent.rectangularMatrixMultiplicationExponent ℚ 0 :=
  rectangularOperationRankBridge ℚ 0 le_rfl

public theorem real_square :
    squareMatrixMultiplicationCircuitExponent ℝ =
      MatrixMultiplicationExponent.rectangularMatrixMultiplicationExponent ℝ 1 :=
  rectangularOperationRankBridge ℝ 1 zero_le_one

end CSLibExtTest.Complexity.Algebraic.DualMatrixMultiplicationBoundsRectangularOperationRankBridge
