/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ConsecutiveBernoulliNumbers

open MetaMathlibExt

-- The k = 0 term fixes the sign convention for B₁.
example : bernoulli 0 + bernoulli 1 = 1 / 2 := by
  rw [bernoulli_add_bernoulli_succ_eq_sum_stirlingSecond 0]
  norm_num

-- At n = 3 the three nonzero terms have alternating signs.
example : bernoulli 3 + bernoulli 4 = -(1 / 30) := by
  rw [bernoulli_add_bernoulli_succ_eq_sum_stirlingSecond 3]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond, Nat.factorial]
