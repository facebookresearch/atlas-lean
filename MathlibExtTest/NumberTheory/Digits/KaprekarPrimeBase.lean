/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.KaprekarPrimeBase

open Function MetaMathlibExt

-- In the composite base 9, every cycle falls strictly short of the bound 4.
example {d : ℕ × ℕ} (hd : d ∈ kaprekarFourDigitStates 9)
    (hp : d ∈ periodicPts (kaprekarFourDigitStep 9)) :
    minimalPeriod (kaprekarFourDigitStep 9) d < 4 := by
  obtain ⟨hbound, hprime⟩ := kaprekar_minimalPeriod_le_and_prime_of_eq 9 (by decide) (by decide)
  exact lt_of_le_of_ne (hbound d hd hp) fun heq =>
    (by decide : ¬ Nat.Prime 9) (hprime ⟨d, hd, heq⟩)
