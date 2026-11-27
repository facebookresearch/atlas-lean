/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CubeRotationPPositions

/-!
# Tests for P-positions of rotation Nim on a cube

These examples exercise both conclusions, including a tied zero minimum and a
unique positive minimum among the opposite-pair sums.
-/

namespace MathlibExtTest.Combinatorics.CubeRotationPPositions

open MetaMathlibExt

-- Equal pair sums do not require equal counts on opposite faces.
example (q : Fin 6 → ℕ) (h : CubeRotationMove ![4, 1, 2, 0, 3, 2] q) :
    ¬ (q 0 + q 3 = q 1 + q 4 ∧ q 1 + q 4 = q 2 + q 5) := by
  exact cubeRotationNim_pPositions.1 _ _ (by decide) h

-- Two pairs are already empty; the remaining token can be removed.
example : ∃ q, CubeRotationMove ![0, 0, 0, 0, 0, 1] q ∧
    q 0 + q 3 = q 1 + q 4 ∧ q 1 + q 4 = q 2 + q 5 := by
  exact cubeRotationNim_pPositions.2 _ (by decide)

-- The middle pair has the unique minimum sum, and both other sums must drop.
example : ∃ q, CubeRotationMove ![3, 1, 2, 2, 1, 4] q ∧
    q 0 + q 3 = q 1 + q 4 ∧ q 1 + q 4 = q 2 + q 5 := by
  exact cubeRotationNim_pPositions.2 _ (by decide)

end MathlibExtTest.Combinatorics.CubeRotationPPositions
