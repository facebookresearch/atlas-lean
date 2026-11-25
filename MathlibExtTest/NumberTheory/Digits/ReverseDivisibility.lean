/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.Digits.ReverseDivisibility

open MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

-- In base five, 3100 reverses to 13, and 5 is neither 1 nor -1 modulo 8.
example : Nat.reverseDigits 5 400 = 8 ∧ 8 ∣ Nat.reverseDigits 5 400 :=
  ⟨by decide, dvd_reverseDigits_of_dvd 5 8 (by decide) (by decide) 400 (by decide)⟩

-- Zero has an empty digit list, including in the smallest permitted base.
example : 3 ∣ Nat.reverseDigits 2 0 :=
  dvd_reverseDigits_of_dvd 2 3 (by decide) (by decide) 0 (dvd_zero _)
