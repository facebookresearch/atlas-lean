/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SabarFineNumberDifference
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.SabarFineNumberDifference` -/

namespace MathlibExtTest.SabarFineNumberDifference

open MetaMathlibExt

-- The statement of the source's Theorem 4, with named arguments.
example (n : ℕ) (hn : 2 ≤ n) :
    fineNumber n = (sabarNumber (2 * n) (n + 1) - sabarNumber (2 * n) (n - 1) : ℤ) :=
  fineNumber_eq_sabarNumber_sub (n := n) (hn := hn)

-- Row `10` of the source's Table 1: `F(5) = s(10, 6) - s(10, 4) = 147 - 129 = 18`.
example : fineNumber 5 = 18 := by
  rw [fineNumber_eq_sabarNumber_sub 5 (by decide)]
  have h₆ : sabarNumber 10 6 = 147 := by decide +kernel
  have h₄ : sabarNumber 10 4 = 129 := by decide +kernel
  norm_num [h₆, h₄]

-- An independent check by evaluating both sides for `2 ≤ n ≤ 7`: `F(n) = 1, 2, 6, 18, 57, 186`.
example : ∀ n ∈ Finset.Icc 2 7,
    fineNumber n = (sabarNumber (2 * n) (n + 1) - sabarNumber (2 * n) (n - 1) : ℤ) := by
  decide +kernel

example : (List.range' 2 6).map fineNumber = [1, 2, 6, 18, 57, 186] := by
  decide +kernel

-- The identity also holds at `n = 1`, where `F(1) = 0 = s(2, 2) - s(2, 0)`.
example : fineNumber 1 = 0 ∧ sabarNumber 2 2 = 0 ∧ sabarNumber 2 0 = 0 := by
  decide +kernel

-- It fails at `n = 0`: `F(0) = 1`, but `s(0, 1)` and `s(0, 0)` are empty sums.
example : fineNumber 0 = 1 ∧
    (sabarNumber (2 * 0) (0 + 1) - sabarNumber (2 * 0) (0 - 1) : ℤ) = 0 := by
  decide +kernel

end MathlibExtTest.SabarFineNumberDifference
