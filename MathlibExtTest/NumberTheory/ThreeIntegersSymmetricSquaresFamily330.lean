/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresFamily330

/-! # Tests for Choudhry's family (3.30) of square triples -/

namespace MathlibExtTest.NumberTheory.ThreeIntegersSymmetricSquaresFamily330

open MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

-- This is the triple in Choudhry's Table 1 and checks the exponent in the third entry.
example : HasSquareElementarySymmetricFunctions 11025 19600 82944 ∧
    IsSquare (11025 : ℤ) ∧ IsSquare (19600 : ℤ) ∧ IsSquare (82944 : ℤ) :=
  hasSquareElementarySymmetricFunctions_family330_and_entries_square 1 2

-- Equal parameters make the first and third entries vanish; zero is allowed as a square.
example : HasSquareElementarySymmetricFunctions 0 256 0 ∧
    IsSquare (0 : ℤ) ∧ IsSquare (256 : ℤ) ∧ IsSquare (0 : ℤ) :=
  hasSquareElementarySymmetricFunctions_family330_and_entries_square 1 1

end MathlibExtTest.NumberTheory.ThreeIntegersSymmetricSquaresFamily330
