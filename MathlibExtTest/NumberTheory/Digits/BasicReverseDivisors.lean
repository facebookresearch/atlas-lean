/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.Digits.BasicReverseDivisors

open MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

-- At the lower endpoint the middle block of nines is empty.
example : (Nat.digits 10 1089).length = 4 ∧ Nat.reverseDigits 10 1089 = 9801 ∧
    (Nat.digits 10 2178).length = 4 ∧ Nat.reverseDigits 10 2178 = 8712 :=
  basic_reverseDivisors (k := 2) (hk := by decide)

-- Two nines between the outer pairs give six-digit reverse divisors.
example : (Nat.digits 10 109989).length = 6 ∧ Nat.reverseDigits 10 109989 = 989901 ∧
    (Nat.digits 10 219978).length = 6 ∧ Nat.reverseDigits 10 219978 = 879912 :=
  basic_reverseDivisors (k := 4) (hk := by decide)
