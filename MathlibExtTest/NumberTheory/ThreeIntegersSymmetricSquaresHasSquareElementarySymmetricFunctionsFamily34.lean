/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresHasSquareElementarySymmetricFunctionsFamily34

/-! # Tests for Choudhry's family (3.4) with square symmetric functions -/

namespace MathlibExtTest.NumberTheory
namespace ThreeIntegersSymmetricSquaresHasSquareElementarySymmetricFunctionsFamily34

open MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

-- A nondegenerate member of the family: `(s, t) = (2, 1)` gives `(320, 80, 225)`.
example : HasSquareElementarySymmetricFunctions 320 80 225 := by
  convert hasSquareElementarySymmetricFunctions_family34 2 1 using 1 <;> norm_num

-- Degenerate parameters `(s, t) = (0, 1)` give `(0, 0, 1)`.
example : HasSquareElementarySymmetricFunctions 0 0 1 := by
  convert hasSquareElementarySymmetricFunctions_family34 0 1 using 1 <;> norm_num

-- Corollary: the sum of the `(320, 80, 225)` instance is the square `625 = 25 ^ 2`.
example : IsSquare ((320 : ℤ) + 80 + 225) := by
  have h : HasSquareElementarySymmetricFunctions 320 80 225 := by
    convert hasSquareElementarySymmetricFunctions_family34 2 1 using 1 <;> norm_num
  exact h.1

end ThreeIntegersSymmetricSquaresHasSquareElementarySymmetricFunctionsFamily34
end MathlibExtTest.NumberTheory
