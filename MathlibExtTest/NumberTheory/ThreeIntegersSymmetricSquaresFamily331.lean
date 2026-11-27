/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresFamily331

/-! # Tests for Choudhry's family (3.31) of square triples with square symmetric functions -/

namespace MathlibExtTest.NumberTheory.ThreeIntegersSymmetricSquaresFamily331

open MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

-- Choudhry's Table 1 lists this triple at `(m, n) = (1, 2)`.
example : HasSquareElementarySymmetricFunctions 9216 5184 1225 ∧
    IsSquare (9216 : ℤ) ∧ IsSquare (5184 : ℤ) ∧ IsSquare (1225 : ℤ) := by
  exact hasSquareElementarySymmetricFunctions_family331_and_entries_square 1 2

-- Opposite nonzero parameters make `m ^ 2 - n ^ 2` vanish.
example : HasSquareElementarySymmetricFunctions 0 0 64 ∧
    IsSquare (0 : ℤ) ∧ IsSquare (0 : ℤ) ∧ IsSquare (64 : ℤ) := by
  exact hasSquareElementarySymmetricFunctions_family331_and_entries_square 1 (-1)

end MathlibExtTest.NumberTheory.ThreeIntegersSymmetricSquaresFamily331
