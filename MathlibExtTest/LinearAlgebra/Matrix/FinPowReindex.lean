/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.FinPowReindex

/-!
# Tests for power-successor reindexing

Concrete examples over integers exercising block reindexing.
-/

set_option autoImplicit false

private def testM : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![0, 1, 2, 3], ![4, 5, 6, 7], ![8, 9, 10, 11], ![12, 13, 14, 15]]

example : (finPowSuccEquiv 2 1) 0 = (0, 0) := by decide

example : (finPowSuccEquiv 2 1) 1 = (0, 1) := by decide

example : (finPowSuccEquiv 2 1) 2 = (1, 0) := by decide

example : (finPowSuccEquiv 2 1) 3 = (1, 1) := by decide

example : (matrixFinPowSuccEquiv 2 1 testM) (0, 1) (1, 0) = 6 := by decide

example : (matrixFinPowSuccEquiv 2 1 testM) (0, 1) (1, 0) =
    testM ((finPowSuccEquiv 2 1).symm (0, 1)) ((finPowSuccEquiv 2 1).symm (1, 0)) :=
  matrixFinPowSuccEquiv_apply 2 1 testM (0, 1) (1, 0)

example : (finPowSuccEquiv 2 0) 0 = (0, 0) := by decide

example : (finPowSuccEquiv 2 0) 1 = (1, 0) := by decide

example : Fin (0 ^ (1 + 1)) ≃ Fin 0 × Fin (0 ^ 1) := finPowSuccEquiv 0 1

example : Fin (1 ^ (1 + 1)) ≃ Fin 1 × Fin (1 ^ 1) := finPowSuccEquiv 1 1

example : (finPowSuccEquiv 1 0) 0 = (0, 0) := by decide
