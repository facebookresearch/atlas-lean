/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.LoanableFundsCrowdingOut

import Mathlib.Tactic

/-!
# Tests for loanable-funds crowding out

With `s0 = 0, s1 = 1, i0 = 10, i1 = 1`: `D = 0` gives `r* = 5, I* = 5,
S* = 5`; `D = 2` gives `r* = 6, I* = 4, S* = 6` — crowding out of 1, rate
up 1, saving up 1.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Macro.LoanableFundsCrowdingOut

open MathlibExt.Economics.Macro.LoanableFundsCrowdingOut

-- Test section: concrete values s0 = 0, s1 = 1, i0 = 10, i1 = 1.
-- D = 0 gives r* = 5, I* = 5, S* = 5; D = 2 gives r* = 6, I* = 4, S* = 6.

example : equilibriumRate 0 1 10 1 0 = 5 := by
  unfold equilibriumRate
  norm_num

example : equilibriumRate 0 1 10 1 2 = 6 := by
  unfold equilibriumRate
  norm_num

example : investment 10 1 (equilibriumRate 0 1 10 1 0) = 5 := by
  unfold investment equilibriumRate
  norm_num

example : investment 10 1 (equilibriumRate 0 1 10 1 2) = 4 := by
  unfold investment equilibriumRate
  norm_num

example : saving 0 1 (equilibriumRate 0 1 10 1 0) = 5 := by
  unfold saving equilibriumRate
  norm_num

example : saving 0 1 (equilibriumRate 0 1 10 1 2) = 6 := by
  unfold saving equilibriumRate
  norm_num

example : saving 0 1 (equilibriumRate 0 1 10 1 0) =
    investment 10 1 (equilibriumRate 0 1 10 1 0) + 0 :=
  equilibriumRate_clears_market 0 1 10 1 0 (by norm_num)

example : saving 0 1 (equilibriumRate 0 1 10 1 2) =
    investment 10 1 (equilibriumRate 0 1 10 1 2) + 2 :=
  equilibriumRate_clears_market 0 1 10 1 2 (by norm_num)

example : equilibriumRate 0 1 10 1 0 < equilibriumRate 0 1 10 1 2 :=
  equilibriumRate_strictMono 0 1 10 1 zero_lt_one zero_lt_one
    (show (0 : ℝ) < 2 by norm_num)

example : investment 10 1 (equilibriumRate 0 1 10 1 2) <
    investment 10 1 (equilibriumRate 0 1 10 1 0) :=
  crowdingOut 0 1 10 1 zero_lt_one zero_lt_one (show (0 : ℝ) < 2 by norm_num)

example : saving 0 1 (equilibriumRate 0 1 10 1 0) <
    saving 0 1 (equilibriumRate 0 1 10 1 2) :=
  savingAtEquilibrium_strictMono 0 1 10 1 zero_lt_one zero_lt_one
    (show (0 : ℝ) < 2 by norm_num)

end MathlibExtTest.Economics.Macro.LoanableFundsCrowdingOut
