/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.BernoulliStirlingSum

open MathlibExt.NumberTheory.BernoulliSecondKindWanted

-- At degree zero the empty partition contributes one.
example : bernoulli 0 = 1 := by
  rw [bernoulli_eq_sum_stirlingSecond]
  norm_num [Nat.stirlingSecond]

-- Degree one distinguishes the two Bernoulli sign conventions.
example : bernoulli 1 = -1 / 2 := by
  rw [bernoulli_eq_sum_stirlingSecond]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond, Nat.factorial]

-- The two nonzero terms in degree two have opposite signs.
example : bernoulli 2 = 1 / 6 := by
  rw [bernoulli_eq_sum_stirlingSecond]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond, Nat.factorial]
