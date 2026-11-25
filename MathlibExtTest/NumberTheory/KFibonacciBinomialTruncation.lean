/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.KFibonacciBinomialTruncation

/-! # Tests for the initial values of the truncated binomial sums -/

open MetaMathlibExt

-- Consecutive indices on either side of the first correction for the tribonacci case.
example : kFibonacciBinomialTruncation 3 4 = 4 := by
  exact (kFibonacciBinomialTruncation_initial_values 3 (by decide)).1 4 (by decide) (by decide)

example : kFibonacciBinomialTruncation 3 5 = 7 := by
  exact (kFibonacciBinomialTruncation_initial_values 3 (by decide)).2.trans (by norm_num)
