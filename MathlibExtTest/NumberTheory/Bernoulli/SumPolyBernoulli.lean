/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.SumPolyBernoulli
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The polynomial difference at the smallest admissible index, computed directly.
example : polyBernoulliPoly 2 2 1 - polyBernoulli 2 2 = 3 / 2 := by
  norm_num [polyBernoulliPoly, polyBernoulli, Finset.sum_range_succ, Nat.choose,
    Nat.stirlingSecond, Nat.factorial]

-- The sum through index four includes the negative terms at indices one and four.
example : polyBernoulliPoly 4 2 1 + bernoulli 4 - polyBernoulli 4 2 - 1 = 19 / 30 := by
  rw [← sum_bernoulli_eq_polyBernoulli 4 (by decide)]
  norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli, bernoulli'_three, bernoulli'_four]
