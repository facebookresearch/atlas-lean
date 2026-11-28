/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Data.Nat.Digits.Div

-- The base-five expansion of 87 is 322, with its least significant digit first in Lean.
example : Nat.digits 5 (87 / 5) = [2, 3] ∧ Nat.digits 5 (87 / 5 ^ 3) = [] := by
  decide

-- Check the public digit-division lemma at a quotient with a nonempty expansion.
example : Nat.digits 5 (87 / 5 ^ 2) = [3] := by
  rw [Nat.digits_div_pow (by decide)]
  decide
