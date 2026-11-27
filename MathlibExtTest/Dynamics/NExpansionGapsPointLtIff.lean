/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.NExpansionGapsPointLtIff
import Mathlib.Tactic.IntervalCases

/-! # Tests for `MathlibExt.Dynamics.NExpansionGapsPointLtIff` -/

namespace MathlibExtTest.Dynamics.NExpansionGapsPointLtIff

open MetaMathlibExt

-- Test section: the word recursion used in the proof of the comparison theorem.
example : idealPeriodWord 5 = idealPeriodWord 4 ++ idealPeriodWord 3 ++ idealPeriodWord 3 := by
  decide

example : idealPeriodWord 6 = idealPeriodWord 5 ++ idealPeriodWord 4 ++ idealPeriodWord 4 := by
  decide

-- Test section: digit string lengths are odd, as used for the parity of the
-- first-difference index.
example : Odd (idealPeriodWord 5).flatten.length := by
  decide

-- Test section: the periodic digit sequences of `d_1` and `d_3` first differ
-- at index `6`, with the values `1` and `2`.
example : ((idealPeriodWord 1).flatten.getD (6 % (idealPeriodWord 1).flatten.length) 0 : ℤ) = 1 ∧
    ((idealPeriodWord 3).flatten.getD (6 % (idealPeriodWord 3).flatten.length) 0 : ℤ) = 2 := by
  decide

example (i : ℕ) (hi : i < 6) :
    ((idealPeriodWord 1).flatten.getD (i % (idealPeriodWord 1).flatten.length) 0 : ℤ) =
      ((idealPeriodWord 3).flatten.getD (i % (idealPeriodWord 3).flatten.length) 0 : ℤ) := by
  interval_cases i <;> decide

-- Test section: the periodic digit sequences of `d_2` and `d_4` first differ
-- at index `13`, with the values `2` and `1`.
example : ((idealPeriodWord 2).flatten.getD (13 % (idealPeriodWord 2).flatten.length) 0 : ℤ) = 2 ∧
    ((idealPeriodWord 4).flatten.getD (13 % (idealPeriodWord 4).flatten.length) 0 : ℤ) = 1 := by
  decide

-- Test section: the periodic digit sequences of `d_3` and `d_4` first differ
-- at index `30`, with the values `1` and `2`.
example : ((idealPeriodWord 3).flatten.getD (30 % (idealPeriodWord 3).flatten.length) 0 : ℤ) = 1 ∧
    ((idealPeriodWord 4).flatten.getD (30 % (idealPeriodWord 4).flatten.length) 0 : ℤ) = 2 := by
  decide

-- Test section: using the comparison theorem with period words `d_2` and `d_1`.
example {N : ℕ} {α : ℝ} (hα : 0 < α) (hαN : α ≤ Real.sqrt N - 1) {x y : ℝ}
    (hx : x ∈ Set.Icc α (α + 1)) (hy : y ∈ Set.Icc α (α + 1))
    (hxd : ∀ i, nExpansionDigit N α ((nExpansionMap N α)^[i] x) =
      ((idealPeriodWord 2).flatten.getD (i % (idealPeriodWord 2).flatten.length) 0 : ℤ))
    (hyd : ∀ i, nExpansionDigit N α ((nExpansionMap N α)^[i] y) =
      ((idealPeriodWord 1).flatten.getD (i % (idealPeriodWord 1).flatten.length) 0 : ℤ)) :
    x < y :=
  (idealPeriodWord_point_lt_iff hα hαN (by norm_num) (by norm_num) hx hy hxd hyd).mpr
    (by norm_num)

end MathlibExtTest.Dynamics.NExpansionGapsPointLtIff
