/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.LoanAmortization
import Mathlib.Tactic.NormNum

/-!
# Tests for loan amortization

A loan of `100` at `r = 1/10` repaid by `60` then `55` has balances `50`, `0`; each period
repays principal `50`, and the principal sum is `100` by `sum_principalRepaid_eq`. An
interest-only schedule (`P = 10`) keeps the balance at `100`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.LoanAmortization

open MathlibExt.Economics.Finance

example : loanBalance (1 / 10 : ℝ) 100 (fun t => if t = 1 then (60 : ℝ) else 55) 1 = 50 := by
  simp [loanBalance]
  norm_num

example : loanBalance (1 / 10 : ℝ) 100 (fun t => if t = 1 then (60 : ℝ) else 55) 2 = 0 := by
  simp [loanBalance]
  norm_num

example : principalRepaid (1 / 10 : ℝ) 100 (fun t => if t = 1 then (60 : ℝ) else 55) 0 = 50 := by
  simp [principalRepaid, loanBalance]
  norm_num

example : principalRepaid (1 / 10 : ℝ) 100 (fun t => if t = 1 then (60 : ℝ) else 55) 1 = 50 := by
  simp [principalRepaid, loanBalance]
  norm_num

example : ∑ t ∈ Finset.range 2, principalRepaid (1 / 10 : ℝ) 100 (fun t => if t = 1 then (60 : ℝ) else 55) t = 100 := by
  have hn : loanBalance (1 / 10 : ℝ) 100 (fun t => if t = 1 then (60 : ℝ) else 55) 2 = 0 := by
    simp [loanBalance]
    norm_num
  exact sum_principalRepaid_eq _ _ _ _ hn

example : loanBalance (1 / 10 : ℝ) 100 (fun _ => (10 : ℝ)) 3 = 100 := by
  simp [loanBalance]
  norm_num

end MathlibExtTest.Economics.Finance.LoanAmortization
