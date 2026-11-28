/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HigherANumbersDeltaDigitCriterion

/-!
# Tests for the digit criterion for the rounding indicator

Check the digits by exact computation and the base-5 indicator values by the direct
lexicographic calculation in `higherANumberDelta_five_four`, independently of the criterion.
Then exercise the criterion as a client in base 5 and base 2.
-/

namespace MathlibExtTest.NumberTheory.HigherANumbersDeltaDigitCriterion

open MetaMathlibExt

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

-- In base 5, τ = 3/2 has units digit 1 and first fractional digit 2.
example : basePDigit 5 (towerTau 5 4 * 1) 0 = 1 ∧
    basePDigit 5 (towerTau 5 4 * 1) (-1) = 2 ∧ higherANumberDelta 5 4 1 = 1 :=
  ⟨by decide +kernel, by decide +kernel, higherANumberDelta_five_four.1⟩

-- For 2τ = 3 the order is reversed: the units digit is 3 and the fractional digit is 0.
example : basePDigit 5 (towerTau 5 4 * 2) 0 = 3 ∧
    basePDigit 5 (towerTau 5 4 * 2) (-1) = 0 ∧ higherANumberDelta 5 4 2 = 0 :=
  ⟨by decide +kernel, by decide +kernel, higherANumberDelta_five_four.2⟩

example : higherANumberDelta 5 4 1 = 1 :=
  (higherANumberDelta_eq_one_iff 5 4 (by decide) (i := 1) (by decide)).mp (by decide +kernel)

-- The binary case τ = 3 also has a larger units digit than fractional digit.
example : ¬ basePDigit 2 (towerTau 2 1 * 1) 0 < basePDigit 2 (towerTau 2 1 * 1) (-1) := by
  decide +kernel

example : higherANumberDelta 2 1 1 ≠ 1 :=
  mt (higherANumberDelta_eq_one_iff 2 1 (by decide) (i := 1) (by decide)).mpr (by decide +kernel)

end MathlibExtTest.NumberTheory.HigherANumbersDeltaDigitCriterion
