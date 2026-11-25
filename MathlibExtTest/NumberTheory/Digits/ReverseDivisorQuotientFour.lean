/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.Digits.ReverseDivisorQuotientFour

open MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

example : ¬ HasPropertyPStar 2178 :=
  not_hasPropertyPStar_of_quotient_four 2178 (by decide) (by decide)

-- The trailing zero of the multiple disappears when its digits are reversed.
example : Nat.reverseDigits 10 (5 * 2178) = 9801 ∧ ¬ 2178 ∣ 9801 := by decide

-- Zero satisfies the reversal equation and does have the property.
example : Nat.reverseDigits 10 0 = 4 * 0 ∧ HasPropertyPStar 0 := by
  refine ⟨by decide, fun m hm => ?_⟩
  rw [Nat.zero_dvd.mp hm]
  decide
