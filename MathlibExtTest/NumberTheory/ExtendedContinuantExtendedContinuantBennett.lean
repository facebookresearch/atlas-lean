/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ExtendedContinuantExtendedContinuantBennett

/-!
# Tests for Bennett's identity

These tests specialize Bennett's identity to indices of both signs.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 3.
-/

namespace MathlibExtTest.NumberTheory.ExtendedContinuantExtendedContinuantBennett

open MetaMathlibExt

example (x : ℤ → ℤ) :
    extendedContinuant x 3 (-2) - extendedContinuant x 1 0 * extendedContinuant x (-5) 1 -
      x 1 * x (-2) = 0 := by
  simpa [Int.negOnePow, extendedContinuant_neg_one, extendedContinuant_zero, sub_eq_add_neg] using
    extendedContinuant_bennett x (-2) 0 1 3

example :
    ((-4 : ℤ).negOnePow : ℤ) * extendedContinuant id (-1) (-3) *
        extendedContinuant id 1 (-1) +
      ((1 : ℤ).negOnePow : ℤ) * extendedContinuant id (-3) (-1) *
        extendedContinuant id (-7) 2 +
      ((-1 : ℤ).negOnePow : ℤ) * extendedContinuant id (-6) 2 *
        extendedContinuant id 0 (-3) = 0 := by
  simpa [Int.negOnePow] using extendedContinuant_bennett id (-3) (-1) 2 (-2)

end MathlibExtTest.NumberTheory.ExtendedContinuantExtendedContinuantBennett
