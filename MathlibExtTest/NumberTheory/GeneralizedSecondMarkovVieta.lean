/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedSecondMarkovVieta

namespace MetaMathlibExt.genSecondMarkov_vieta

private def Solves (k : ℕ) (a b c : ℤ) : Prop :=
  a ^ 2 + b ^ 2 + c ^ 2 + ((k : ℤ) ^ 2 + 2 * k) * (a + b + c) + 2 * (k : ℤ) ^ 3 +
    3 * (k : ℤ) ^ 2 = a * b * c

-- A solution with a zero coordinate jumps to middle coordinates of opposite signs.
example : Solves 2 (-6) 16 (-4) ∧ Solves 2 (-4) (-2) 0 := by
  have left : (-6 : ℤ) * (-4) - 0 - (2 : ℕ) ^ 2 - 2 * (2 : ℕ) = 16 := by decide
  have right : (-4 : ℤ) * 0 - (-6) - (2 : ℕ) ^ 2 - 2 * (2 : ℕ) = -2 := by decide
  simpa only [Solves, left, right] using
    genSecondMarkov_vieta 2 (a := -6) (b := -4) (c := 0) (by decide)

end MetaMathlibExt.genSecondMarkov_vieta
