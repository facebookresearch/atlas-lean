/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.BasicReverseDivisors

open MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

-- At the smallest exponent the central block of nines is empty.
example : (Nat.digits 10 1089).length = 4 ∧ Nat.reverseDigits 10 1089 = 9801 ∧
    (Nat.digits 10 2178).length = 4 ∧ Nat.reverseDigits 10 2178 = 8712 :=
  basic_reverseDivisors 2 (by decide)

-- This case has two central nines and retains the interior zero in the first family.
example : (Nat.digits 10 109989).length = 6 ∧ Nat.reverseDigits 10 109989 = 989901 ∧
    (Nat.digits 10 219978).length = 6 ∧ Nat.reverseDigits 10 219978 = 879912 :=
  basic_reverseDivisors 4 (by decide)
